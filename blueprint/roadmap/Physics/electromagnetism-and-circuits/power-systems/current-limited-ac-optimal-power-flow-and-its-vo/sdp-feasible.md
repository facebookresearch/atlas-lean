# Feasibility for the semidefinite relaxation

Let an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses and $m$ branches be given, with [bus admittance matrix](admittance.md) $Y$. A complex
$n \times n$ matrix $W$ is feasible for the semidefinite relaxation (SDP) if $W$ is positive
semidefinite, that is Hermitian with $x^{\mathsf H} W x \ge 0$ for every $x \in \mathbb{C}^n$, and,
with the [pairing](pairing.md) $\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$,

- $P^{\min}_k \le \langle A^P_k, W \rangle + P^d_k \le P^{\max}_k$ for every bus $k$;
- $Q^{\min}_k \le \langle A^Q_k, W \rangle + Q^d_k \le Q^{\max}_k$ for every bus $k$;
- $v^{\min}_k \le \langle E_k, W \rangle \le v^{\max}_k$ for every bus $k$;
- $\langle C_e, W \rangle \le i^{\max}_e$ for every branch $e$,

where $A^P_k$ and $A^Q_k$ are the [active](active-coeff.md) and [reactive](reactive-coeff.md)
coefficient matrices of $Y$ at bus $k$, $E_k$ is the [voltage coefficient matrix](voltage-coeff.md)
and $C_e$ the [branch-current coefficient matrix](branch-current-coeff.md) of the incidence matrix
and branch admittances. No rank condition is imposed. A voltage vector is AC feasible
[exactly when its lift is feasible](ac-feasible-iff-sdp-feasible-voltage-lif.md) here, and for some
instances, such as the [two-bus example](two-bus-rank-two-relaxed-not-lift.md), feasible matrices
that are not lifts exist.
