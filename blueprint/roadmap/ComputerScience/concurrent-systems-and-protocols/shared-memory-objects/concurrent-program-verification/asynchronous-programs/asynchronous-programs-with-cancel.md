# Asynchronous programs with cancel

An asynchronous program has finitely many global states, recursive handlers given by a context-free grammar, and a multiset of pending handler instances; dispatching a handler runs it to completion, changing the global state and posting new instances. With cancel, a handler may also remove all pending instances of a given handler.

**Asynchronous programs.** An asynchronous program $\mathcal{P} = (D, \Sigma, \Sigma_i, G, R, d_0, \mathbf{m}_0)$ consists of a finite set $D$ of global states, a finite alphabet $\Sigma$ of handler names, a finite alphabet $\Sigma_i$ of internal actions disjoint from $\Sigma$, a context-free grammar $G = (\mathcal{X}, \Sigma \cup \Sigma_i, \mathcal{P}_G)$ with a nonterminal $X_\sigma$ for each $\sigma \in \Sigma$, a regular grammar $R = (D, \Sigma \cup \Sigma_i, \delta)$ whose nonterminals are the global states, an initial multiset $\mathbf{m}_0 \in \mathbb{M}[\Sigma]$ of pending handler instances and an initial state $d_0 \in D$. Configurations are pairs $(d, \mathbf{m}) \in D \times \mathbb{M}[\Sigma]$, the initial one being $(d_0, \mathbf{m}_0)$. For $\sigma \in \Sigma$,

$$
(d, \mathbf{m} \oplus [\sigma]) \xrightarrow{\sigma} (d', \mathbf{m} \oplus \mathbf{m}')
$$

if some word $w \in (\Sigma \cup \Sigma_i)^*$ satisfies $X_\sigma \Rightarrow_G^* w$, $d \Rightarrow_R^* w \cdot d'$ and $\mathbf{m}' = \Psi_\Sigma(w)$, the Parikh image of $w$ restricted to $\Sigma$: the dispatched handler $\sigma$ executes one of its words, the global state follows $R$, and every handler name in $w$ is posted.

**Cancel.** In an asynchronous program with cancel, $\mathcal{P} = (D, \Sigma \cup \bar{\Sigma}, \Sigma_i, G, R, d_0, \mathbf{m}_0)$, each $\sigma \in \Sigma$ has a cancel symbol $\bar{\sigma} \in \bar{\Sigma}$, and $G$ and $R$ are over $\Gamma = \Sigma_i \cup \Sigma \cup \bar{\Sigma}$. Then $(d, \mathbf{m} \oplus [\sigma]) \xrightarrow{\sigma} (d', \mathbf{m}')$ if some $w \in \Gamma^*$ satisfies $X_\sigma \Rightarrow_G^* w$, $d \Rightarrow_R^* w \cdot d'$, and for every $b \in \Sigma$: if $w = w_1 \bar{b} w_2$ with no $\bar{b}$ in $w_2$, then $\mathbf{m}'(b) = \Psi(w_2)(b)$; if $w$ contains no $\bar{b}$, then $\mathbf{m}'(b) = \mathbf{m}(b) + \Psi(w)(b)$. A cancel $\bar{b}$ removes every pending instance of $b$ at that point of the execution.

**Problems.** A run is a finite or infinite sequence of transitions from the initial configuration. For a program (with or without cancel):

- safety (global state reachability): given $d \in D$, is some configuration $(d, \mathbf{m})$ reachable?
- configuration reachability: given $(d, \mathbf{m})$, is it reachable?
- boundedness: is the set of reachable configurations finite?
- non-termination: is there an infinite run?

## Depends on

- [Context-free languages](../../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [Parikh image of a language](../../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/parikh-image.md)

## Proof depends on

None.

## Expansion

A control-flow graph program with finite-data abstraction yields an asynchronous program: nonterminals are the control points, an asynchronous call to $\sigma$ contributes a production $X \to \sigma \cdot Y$, a synchronous call contributes $X \to v^e_\sigma \cdot Y$, and $R$ encodes the abstract transfer function on $D$. Without cancel, safety, boundedness and configuration reachability reduce in polynomial time to coverability, boundedness and reachability of Petri nets, and safety is EXPSPACE-complete. Cancellation makes the order of posts within one handler execution matter.

## Sources

- Pierre Ganty and Rupak Majumdar, "Algorithmic verification of asynchronous programs", *ACM Transactions on Programming Languages and Systems* 34(1), Article 6, 48 pages, 2012, <https://doi.org/10.1145/2160910.2160915>; read as arXiv:1011.0551v3, <https://arxiv.org/abs/1011.0551v3>: Section 4.1 (asynchronous programs), Section 4.4 (Definitions 4.6 and 4.7, the problems), Section 7.1 (asynchronous programs with cancel and the problems for them), Section 6.1 (safety, boundedness and configuration reachability).
