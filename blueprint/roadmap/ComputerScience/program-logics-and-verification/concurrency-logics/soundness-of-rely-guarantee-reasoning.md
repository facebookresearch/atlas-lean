# Soundness of rely-guarantee reasoning

Use the commands, computations and satisfaction of $(\mathit{pre}, R, G, \mathit{post})$ from the
[trace model of rely-guarantee reasoning](trace-model-of-rely-guarantee-reasoning.md). The rely-guarantee proof system
derives judgments $C\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$ for components by these rules:

- Basic: if $\mathit{pre} \subseteq \{s \mid f\,s \in \mathit{post}\}$, $\{(s, t) \mid s \in \mathit{pre},\ t = f\,s \text{ or } t = s\} \subseteq G$, and $\mathit{pre}$ and
  $\mathit{post}$ are stable under $R$, then $\mathbf{basic}\ f\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$.
- Sequence: from $C_1\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{mid}]$ and $C_2\ \mathbf{sat}\ [\mathit{mid}, R, G, \mathit{post}]$ infer
  $C_1; C_2\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$.
- Conditional: if $\mathit{pre}$ is stable under $R$, $G$ is reflexive, $C_1\ \mathbf{sat}\ [\mathit{pre} \cap b, R, G, \mathit{post}]$ and
  $C_2\ \mathbf{sat}\ [\mathit{pre} \setminus b, R, G, \mathit{post}]$, then the conditional satisfies $[\mathit{pre}, R, G, \mathit{post}]$.
- While: if $\mathit{pre}$ and $\mathit{post}$ are stable under $R$, $\mathit{pre} \setminus b \subseteq \mathit{post}$, $G$ is reflexive and
  $C\ \mathbf{sat}\ [\mathit{pre} \cap b, R, G, \mathit{pre}]$, then $\mathbf{while}\ b\ \mathbf{do}\ C\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$.
- Await: if $\mathit{pre}$ and $\mathit{post}$ are stable under $R$ and for every state $V$,
  $C\ \mathbf{sat}\ [\mathit{pre} \cap b \cap \{V\}, \mathrm{id}, \Sigma \times \Sigma, \{s \mid (V, s) \in G\} \cap \mathit{post}]$, then
  $\mathbf{await}\ b\ \mathbf{then}\ C\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$.
- Consequence: from $C\ \mathbf{sat}\ [\mathit{pre}', R', G', \mathit{post}']$ with $\mathit{pre} \subseteq \mathit{pre}'$, $R \subseteq R'$, $G' \subseteq G$ and
  $\mathit{post}' \subseteq \mathit{post}$, infer $C\ \mathbf{sat}\ [\mathit{pre}, R, G, \mathit{post}]$.

The parallel rule: from $C_i\ \mathbf{sat}\ [\mathit{pre}_i, R_i, G_i, \mathit{post}_i]$ for $i = 1, \dots, n$ with
$R \cup \bigcup_{j \ne i} G_j \subseteq R_i$ for every $i$, $\bigcup_j G_j \subseteq G$, $\mathit{pre} \subseteq \bigcap_i \mathit{pre}_i$ and
$\bigcap_i \mathit{post}_i \subseteq \mathit{post}$, infer that $C_1 \parallel \dots \parallel C_n$ satisfies $[\mathit{pre}, R, G, \mathit{post}]$.

**Theorem.** Every derivable component judgment is satisfied by its command, and every parallel judgment derived by
the parallel rule from derivable component judgments is satisfied by the parallel program, in the interleaving
computation semantics.

## Depends on

- [Trace model of rely-guarantee reasoning](trace-model-of-rely-guarantee-reasoning.md)

## Proof depends on

- [Trace model of rely-guarantee reasoning](trace-model-of-rely-guarantee-reasoning.md)

## Sources

- L. Prensa Nieto, *Hoare Logic for Parallel Programs*, Isabelle/HOL theory library (HOL-Hoare_Parallel), document of May 23, 2024, Section 3.4 (rghoare and par-rghoare rules) and Section 3.5 (theorems rgsound and par-rgsound).
- C. B. Jones, "Tentative steps toward a development method for interfering programs", *ACM Transactions on Programming Languages and Systems* 5(4):596–619, 1983.
- K. R. Apt, F. S. de Boer and E.-R. Olderog, *Verification of Sequential and Concurrent Programs*, 3rd ed., Springer, 2009.
