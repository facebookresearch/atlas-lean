# The anti-Fibonacci construction

For each $n \ge 0$, entry $n$ of the construction is the
triple $(A_{n+1}, B_{n+1}, C_{n+1})$ of natural numbers together with the finite set $U_{n+1}$ of
values used so far. Entry $0$ is $(1, 2, 3)$ with $U_1 = \{1, 2, 3\}$. For $n \ge 1$, $A_{n+1}$ is
the least positive integer not in $U_n$, $B_{n+1}$ is the least positive integer not in
$U_n \cup \{A_{n+1}\}$, $C_{n+1} = A_{n+1} + B_{n+1}$, and
$U_{n+1} = U_n \cup \{A_{n+1}, B_{n+1}, C_{n+1}\}$.

The $C_n$ are the anti-Fibonacci numbers (OEIS A075326 without its initial $0$) and the missing
numbers $A_1, B_1, A_2, B_2, \dots$ are the non-anti-Fibonacci numbers $Y_1, Y_2, \dots$
(OEIS A249031).

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Section 4.
