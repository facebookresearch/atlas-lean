# Soundness of incorrectness logic

Commands are built from $\mathbf{skip}$, $\mathbf{error}()$, $\mathbf{assume}\ B$, assignment $x = e$, nondeterministic
assignment $x = \mathbf{nondet}()$, local variable blocks $\mathbf{local}\ x.\,C$, sequencing $C_1; C_2$, choice
$C_1 + C_2$ and Kleene iteration $C^\star$. States are functions $\Sigma = \mathrm{Var} \to \mathrm{Val}$, and an assertion is any
subset of $\Sigma$. Each command denotes two relations $[\![C]\!]_{\mathit{ok}}, [\![C]\!]_{\mathit{er}} \subseteq \Sigma \times \Sigma$:

- $[\![\mathbf{skip}]\!]_{\mathit{ok}}$ is the identity and $[\![\mathbf{skip}]\!]_{\mathit{er}} = \emptyset$; $[\![\mathbf{error}()]\!]_{\mathit{ok}} = \emptyset$ and
  $[\![\mathbf{error}()]\!]_{\mathit{er}}$ is the identity;
- $[\![\mathbf{assume}\ B]\!]_{\mathit{ok}} = \{(\sigma, \sigma) \mid [\![B]\!]\sigma = \mathrm{true}\}$ and $[\![\mathbf{assume}\ B]\!]_{\mathit{er}} = \emptyset$;
- $[\![x = e]\!]_{\mathit{ok}} = \{(\sigma, \sigma[x \mapsto [\![e]\!]\sigma])\}$, $[\![x = \mathbf{nondet}()]\!]_{\mathit{ok}} = \{(\sigma, \sigma[x \mapsto v]) \mid v \in \mathrm{Val}\}$, and both
  have empty $\mathit{er}$ relation;
- $[\![\mathbf{local}\ x.\,C]\!]_\epsilon = \{(\sigma[x \mapsto v], \sigma'[x \mapsto v]) \mid (\sigma, \sigma') \in [\![C]\!]_\epsilon,\ v \in \mathrm{Val}\}$;
- $[\![C_1 + C_2]\!]_\epsilon = [\![C_1]\!]_\epsilon \cup [\![C_2]\!]_\epsilon$ and $[\![C^\star]\!]_\epsilon = \bigcup_{i \in \mathbb{N}} [\![C^i]\!]_\epsilon$, where
  $C^0 = \mathbf{skip}$ and $C^{i+1} = C; C^i$;
- $[\![C_1; C_2]\!]_\epsilon = [\![C_1]\!]_{\mathit{ok}} \mathbin{;} [\![C_2]\!]_\epsilon$ (relational composition), together with $[\![C_1]\!]_{\mathit{er}}$ when $\epsilon = \mathit{er}$.

For $\epsilon \in \{\mathit{ok}, \mathit{er}\}$, the triple $[p]\, C\, [\epsilon : q]$ is *true* when every state in $q$ is reachable from
some state in $p$: for every $\sigma' \in q$ there is $\sigma \in p$ with $(\sigma, \sigma') \in [\![C]\!]_\epsilon$.

**Theorem.** Every triple derivable from the following axioms and rules is true.

- Empty: $[p]\, C\, [\epsilon : \mathrm{false}]$. Consequence: from $[p]\, C\, [\epsilon : q]$ with $p \subseteq p'$ and $q' \subseteq q$,
  infer $[p']\, C\, [\epsilon : q']$. Disjunction: from $[p_1]\, C\, [\epsilon : q_1]$ and $[p_2]\, C\, [\epsilon : q_2]$, infer
  $[p_1 \cup p_2]\, C\, [\epsilon : q_1 \cup q_2]$.
- Unit: $[p]\, \mathbf{skip}\, [\mathit{ok} : p]$ and $[p]\, \mathbf{skip}\, [\mathit{er} : \mathrm{false}]$. Error: $[p]\, \mathbf{error}()\, [\mathit{ok} : \mathrm{false}]$
  and $[p]\, \mathbf{error}()\, [\mathit{er} : p]$. Assume: $[p]\, \mathbf{assume}\ B\, [\mathit{ok} : p \wedge B]$ and
  $[p]\, \mathbf{assume}\ B\, [\mathit{er} : \mathrm{false}]$.
- Sequencing: from $[p]\, C_1\, [\mathit{er} : r]$ infer $[p]\, C_1; C_2\, [\mathit{er} : r]$; from $[p]\, C_1\, [\mathit{ok} : q]$ and
  $[q]\, C_2\, [\epsilon : r]$ infer $[p]\, C_1; C_2\, [\epsilon : r]$. Choice: from $[p]\, C_i\, [\epsilon : q]$ ($i = 1, 2$) infer
  $[p]\, C_1 + C_2\, [\epsilon : q]$.
- Iteration: $[p]\, C^\star\, [\mathit{ok} : p]$; from $[p]\, C^\star; C\, [\epsilon : q]$ infer $[p]\, C^\star\, [\epsilon : q]$; and, for a
  family $p(n)$ of assertions indexed by natural numbers, from $[p(n)]\, C\, [\mathit{ok} : p(n+1)]$ for every $n$ infer
  $[p(0)]\, C^\star\, [\mathit{ok} : \exists n.\, p(n)]$.
- Assignment: $[p]\, x = e\, [\mathit{ok} : \exists x'.\, p[x'/x] \wedge x = e[x'/x]]$ and $[p]\, x = \mathbf{nondet}()\, [\mathit{ok} : \exists x.\, p]$,
  each with $\mathit{er}$ result $\mathrm{false}$.
- Constancy: from $[p]\, C\, [\epsilon : q]$ infer $[p \wedge f]\, C\, [\epsilon : q \wedge f]$ when no variable assigned in $C$ is free in
  $f$. Local variable: from $[p]\, C(y/x)\, [\epsilon : q]$ infer $[p]\, \mathbf{local}\ x.\, C\, [\epsilon : \exists y.\, q]$ when $y$ is free in
  neither $p$ nor $C$. Substitution: from $[p]\, C\, [\epsilon : q]$ infer the triple with $e$ (respectively a variable $y$
  not free in $p$, $C$, $q$) substituted for $x$, when $e$ and $x$ are not free in $C$.

Here a variable is free in an assertion when the assertion is not invariant under changing that variable, and
substitution in an assertion is the preimage $p[e/x] = \{\sigma \mid \sigma[x \mapsto [\![e]\!]\sigma] \in p\}$, so that $\sigma \in p[e/x]$ exactly when $p$ holds after $x$ is set to the value of $e$ at $\sigma$. In the assignment axiom $x'$ is a fresh variable, free in neither $p$ nor $e$.

## Sources

- P. W. O'Hearn, "Incorrectness logic", *Proceedings of the ACM on Programming Languages* 4(POPL), Article 10, 2020: Figures 2–4, Definitions 1 and 4, Lemma 3 and Theorem 5.
