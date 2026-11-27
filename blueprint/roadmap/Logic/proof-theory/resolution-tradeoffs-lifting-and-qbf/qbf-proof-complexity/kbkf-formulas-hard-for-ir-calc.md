# The Kleine Büning-Karpinski-Flögel formulas are hard for IR-calc

The QBFs $\mathrm{KBKF}(t)$ require refutations of length at least $2^t$ in IR-calc, hence exponential Q-resolution refutations, while they are easy for long-distance and universal Q-resolution.

The formula $\mathrm{KBKF}(t)$ has prefix

$$
\exists y_0, y_{1,0}, y_{1,1}\ \forall x_1\ \exists y_{2,0}, y_{2,1}\ \forall x_2 \dots \forall x_{t-1}\ \exists y_{t,0}, y_{t,1}\ \forall x_t\ \exists y_{t+1} \dots y_{t+t}
$$

and matrix clauses $\{\overline{y}_0\}$, $\{y_0, \overline{y}_{1,0}, \overline{y}_{1,1}\}$, and for $i \in [t-1]$ the clauses $\{y_{i,0}, x_i, \overline{y}_{i+1,0}, \overline{y}_{i+1,1}\}$ and $\{y_{i,1}, \overline{x}_i, \overline{y}_{i+1,0}, \overline{y}_{i+1,1}\}$, together with $\{y_{t,0}, x_t, \overline{y}_{t+1}, \dots, \overline{y}_{t+t}\}$, $\{y_{t,1}, \overline{x}_t, \overline{y}_{t+1}, \dots, \overline{y}_{t+t}\}$ and, for $i \in [t]$, $\{x_i, y_{t+i}\}$ and $\{\overline{x}_i, y_{t+i}\}$.

**Theorem.** Every IR-calc proof of $\mathrm{KBKF}(t)$ has length at least $2^t$. Consequently every Q-resolution refutation of $\mathrm{KBKF}(t)$ has exponential size, and IR-calc simulates neither long-distance Q-resolution nor QU-resolution.

## Expansion

The formulas are false: the existential player must set $y_0 = 0$, then one of $y_{1,0}, y_{1,1}$ to $0$, and the universal player answers each choice by setting $x_i$ so that another pair must be zeroed, until some $y_{t+i}$ is forced to $0$ and a final clause is falsified. The existential player has $2^t$ ways to play, and the universal player must counter each uniquely. A refutation is first transformed, without changing its length, into a proof of $y_0$ from the other clauses, in which every clause has a unique positive literal (its head). To each clause $C$ one assigns a set $\Sigma(C)$ of complete annotations to $x_1, \dots, x_t$: axioms have $\Sigma = \emptyset$, instantiation does not change $\Sigma$, and a resolution step either takes the union of the premises' sets or adds exactly one new annotation. The final clause $y_0$ has all $2^t$ annotations in $\Sigma$, so there are at least $2^t$ resolution steps. Since IR-calc p-simulates Q-resolution, the Q-resolution lower bound follows, while the formulas have short long-distance and QU-resolution refutations.

## Depends on

- [Expansion-based QBF calculi: universal expansion resolution and IR-calc](expansion-based-qbf-calculi.md)
- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, L. Chew, M. Janota, "Proof complexity of resolution-based QBF calculi", *STACS 2015*, LIPIcs 30, 76-89, doi:10.4230/LIPIcs.STACS.2015.76 (Definition 1, Lemma 2, Theorem 6, Corollaries 7 and 8, Section 3).
