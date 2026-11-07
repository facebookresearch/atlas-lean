# Anti-Tribonacci construction

Write $\mathrm{mex}(U)$ for the least positive integer not in
a finite set $U$ of natural numbers. Set $(A_1, B_1, C_1, D_1) = (1, 2, 3, 6)$ and
$U_1 = \{1, 2, 3, 6\}$. For $k \ge 1$ let $A_{k+1} = \mathrm{mex}(U_k)$,
$B_{k+1} = \mathrm{mex}(U_k \cup \{A_{k+1}\})$,
$C_{k+1} = \mathrm{mex}(U_k \cup \{A_{k+1}, B_{k+1}\})$, $D_{k+1} = A_{k+1} + B_{k+1} + C_{k+1}$
and $U_{k+1} = U_k \cup \{A_{k+1}, B_{k+1}, C_{k+1}, D_{k+1}\}$. Entry $n$ of the construction is
the pair $((A_{n+1}, B_{n+1}, C_{n+1}, D_{n+1}), U_{n+1})$, where $U_{n+1}$ is the set of all
values used so far.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Section 4.
