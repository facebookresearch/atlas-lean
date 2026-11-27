# Second moment of $\omega_1$ over $h$-free polynomials

Let $F$ be a finite field with $q$
elements, let $h \ge 2$ and let $\varepsilon > 0$. Let $\omega_1(f)$ be the number of monic
irreducible $P$ dividing $f$ exactly once, write $S_h \cap M_n$ for the set of $h$-free monic
polynomials of degree $n$ over $F$ and $|P| = q^{\deg P}$, and let
$B_1 = \gamma + \sum_P (\log(1 - 1/|P|) + 1/|P|)$ be the function field Mertens constant, with
$\gamma$ the Euler–Mascheroni constant, $T_h = \sum_P (|P|^{h-1} - 1)/(|P|(|P|^h - 1))$ and
$U_h = \sum_P (|P|^{h-2}(|P| - 1)/(|P|^h - 1))^2$, all sums over monic irreducible $P$. Then the
mean of $\omega_1^2$ over $S_h \cap M_n$ is $\log^2 n + C_2 \log n + C_3 + O(n^{\varepsilon - 1})$
as $n \to \infty$, where $C_2 = 2(B_1 - T_h) + 1$ and
$C_3 = B_1^2 + B_1 - \pi^2/6 - U_h + T_h^2 - (2B_1 + 1) T_h$.

The printed error $O_\varepsilon(q^n/n^{1-\varepsilon})$ is the error of the unnormalized sum in
the paper's proof; divided by $|S_h \cap M_n| = q^n/\zeta_q(h)$ for $n \ge h$, where
$\zeta_q(h) = (1 - q^{1-h})^{-1}$, it is $O_\varepsilon(n^{\varepsilon-1})$, the order that the
paper's remark (an extra factor $n^\varepsilon$ over the first moment's $O(1/n)$) and its
variance formula state.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 1, Equation (5).
