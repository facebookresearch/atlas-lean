# Combined properties of the voltage lift and the relaxation

Let an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses and $m$ branches be given, with incidence matrix $B$, branch admittances $y$, shunt
admittances $y^{\mathrm{sh}}$ and [bus admittance matrix](admittance.md) $Y$, and let
$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$ be the [pairing](pairing.md). Then
all of the following hold:

- for every $V \in \mathbb{C}^n$, the [voltage lift](voltage-lift.md) $V V^{\mathsf H}$ is positive
  semidefinite;
- for every complex $n \times n$ matrix $A$, the map $W \mapsto \langle A, W \rangle$ is
  real-linear;
- for every bus $k$, the [active](active-coeff.md) and [reactive](reactive-coeff.md) coefficient
  matrices of $Y$ at $k$ and the [voltage coefficient matrix](voltage-coeff.md) $E_k$ are Hermitian;
- for every branch $e$, the [branch-current coefficient matrix](branch-current-coeff.md) of $B$ and
  $y$ at $e$ is Hermitian;
- for every $V \in \mathbb{C}^n$ and every bus $k$, the complex power $V_k \overline{I_k}$ that bus
  $k$ supplies to the network, with
  $I_k = \sum_e B_{ke}\, y_e\, (B^{\mathsf T} V)_e + y^{\mathrm{sh}}_k V_k$, equals the
  [lifted injection](lifted-injection.md) $\sum_j \overline{Y_{kj}}\, W_{kj}$ at
  $W = V V^{\mathsf H}$;
- for every $V \in \mathbb{C}^n$, $V$ is [AC feasible](ac-feasible.md) if and only if
  $V V^{\mathsf H}$ is [feasible for the semidefinite relaxation](sdp-feasible.md);
- for every $V \in \mathbb{C}^n$, the [relaxation cost](sdp-cost.md) of $V V^{\mathsf H}$ equals the
  [AC cost](ac-cost.md) of $V$;
- every real number that is at most the relaxation cost of every relaxation-feasible matrix is at
  most the AC cost of every AC-feasible voltage vector.
