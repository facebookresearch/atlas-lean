# Wild-type and mutant dynamics under mutagenesis

Consider a virus within a host, described by the abundance $x$ of wild type and $y$ of mutants of
interest. Both replicate at rate $b$ with per-base replication fidelity $q = 1 - u$, where $u$ is
the mutation rate per base, and both are cleared at rate $a$. Of the genome's positions, $m$ must
stay unmutated for the progeny to be viable, and $n$ further positions are such that a mutation at
any one of them produces a mutant of the type whose emergence is of concern. Ignoring back
mutation, during a phase with constant clearance rate $a$

$$\begin{aligned}
\dot x &= x\,(b q^{\,m+n} - a), \\
\dot y &= x\,b q^{\,m}\,(1 - q^{\,n}) + y\,(b q^{\,m} - a),
\end{aligned}$$

so the total virus $v = x + y$ obeys $\dot v = v\,(b q^{\,m} - a)$. Starting from $x(0) = 1$,
$y(0) = 0$, the solution at time $T$ is

$$v(T) = e^{(b q^{m} - a)T}, \qquad
x(T) = e^{(b q^{m+n} - a)T}, \qquad
y(T) = e^{(b q^{m} - a)T} - e^{(b q^{m+n} - a)T}.$$

## Proof depends on

- [Global existence and uniqueness for homogeneous linear ODEs](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/exists-unique-has-deriv-at-eq-continuous.md)

## Proof sketch

The wild type keeps its identity only if none of the $m + n$ marked positions mutates, which gives
its growth factor $b q^{m+n}$; any replication that keeps the $m$ lethal positions intact but
changes one of the other $n$ produces a mutant, which is the source term in $\dot y$. Since the
total virus only needs the $m$ lethal positions intact, $v$ obeys a closed linear equation, and the
mutant abundance is the difference between the total and the wild type.

## Sources

- G. Lobinska, Y. Pilpel, M. A. Nowak, "Evolutionary safety of lethal mutagenesis driven by antiviral
  treatment", PLoS Biology 21 (2023) e3002214, Eqs. (23A)-(23C) and (25A)-(25C),
  <https://doi.org/10.1371/journal.pbio.3002214> (PMC10409280).
