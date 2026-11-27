# HyperLTL

A *trace* over a set $AP$ of atomic propositions is an infinite sequence $t \in (2^{AP})^\omega$. *HyperLTL* formulas, over an infinite set of trace variables $\pi$, are

$$\psi ::= \exists \pi.\ \psi \mid \forall \pi.\ \psi \mid \varphi, \qquad \varphi ::= a_\pi \mid \neg\varphi \mid \varphi \vee \varphi \mid \mathbf X\varphi \mid \varphi\ \mathbf U\ \varphi,$$

[linear temporal logic](../linear-temporal-logic/formula.md) with each atomic proposition indexed by a trace variable and a prefix of trace quantifiers. For a set $T$ of traces and a
partial assignment $\Pi$ of traces to variables: $\Pi \models_T \exists\pi.\psi$ iff $\Pi[\pi \mapsto t] \models_T \psi$ for some $t \in T$, dually for $\forall$; $\Pi \models_T a_\pi$ iff $a \in \Pi(\pi)[0]$;
$\Pi \models_T \mathbf X\varphi$ iff $\Pi[1, \infty] \models_T \varphi$; and $\Pi \models_T \varphi_1 \mathbf U \varphi_2$ iff some $i \ge 0$ has $\Pi[i, \infty] \models_T \varphi_2$ and $\Pi[j, \infty] \models_T \varphi_1$ for all $j < i$,
where $\Pi[i, \infty]$ takes the suffix of every assigned trace. $T$ *satisfies* a closed $\psi$ if the empty assignment does, and a [Kripke structure](kripke-structures-with-initial-states.md) $K = (S, s_0, \delta, AP, L)$, with the single initial state $s_0$ (initial set $\{s_0\}$),
transition relation $s' \in \delta(s)$ and total (every state has at least one $\delta$-successor), satisfies $\psi$ if its set of traces $\mathrm{Traces}(K)$ does, the label sequences $L(s_0) L(s_1) L(s_2) \cdots$ of the infinite paths $s_0 s_1 s_2 \cdots$ from the initial state
with $s_{i+1} \in \delta(s_i)$. A closed HyperLTL formula therefore denotes a [hyperproperty](hyperproperties-hypersafety-and-k-safety.md). For example, writing $\pi =_L \pi'$ for $\mathbf G \bigwedge_{a \in L} (a_\pi \leftrightarrow a_{\pi'})$ over a finite set $L$ of low
propositions, observational determinism is $\forall\pi.\forall\pi'.\ \pi[0] =_{L_{\mathrm{in}}} \pi'[0] \to \pi =_{L_{\mathrm{out}}} \pi'$.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Hyperproperties, hypersafety and k-safety](hyperproperties-hypersafety-and-k-safety.md)
- [Kripke structures with initial states](kripke-structures-with-initial-states.md)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 2 (syntax, semantics and Kripke structures) and Section 3 (the sugar $\pi =_P \pi'$ and observational determinism).
