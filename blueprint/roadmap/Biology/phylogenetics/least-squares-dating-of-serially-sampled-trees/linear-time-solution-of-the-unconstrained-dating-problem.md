# Linear-time solution of the unconstrained dating problem

In the setting of the [weighted least-squares dating criterion](weighted-least-squares-dating-criterion.md), for a rooted binary tree with tips of known date, branch lengths $b_i$, weights $w_i > 0$ and parent map $a$, the unconstrained minimizer $(\hat\omega, \hat t_1, \dots, \hat t_{n-1})$ of

$$\varphi(\omega, t) = \sum_{i=2}^{2n-1} w_i\bigl(b_i - \omega(t_i - t_{a(i)})\bigr)^2$$

can be computed in $O(n)$ arithmetic operations:

1. For fixed $\omega > 0$, the stationarity conditions $\partial\varphi/\partial t_i = 0$ say that each internal date is the weighted average of the dates implied by its neighbours: with children $s_1, s_2$ of $i$,

$$t_i \;=\; \frac{w_{s_1}\bigl(t_{s_1} - \tfrac{b_{s_1}}{\omega}\bigr) + w_{s_2}\bigl(t_{s_2} - \tfrac{b_{s_2}}{\omega}\bigr) + w_i\bigl(t_{a(i)} + \tfrac{b_i}{\omega}\bigr)}{w_{s_1} + w_{s_2} + w_i},$$

where the last term is absent at the root.
2. Eliminating dates from the tips upward expresses each internal date in terms of its parent's, $t_i = x_i t_{a(i)} + y_i + z_i/\omega$, and substituting from the root downward gives $t_i(\omega) = u_i + v_i/\omega$ for every node, with $u_i = t_i$ and $v_i = 0$ at tips, all coefficients found in two tree traversals.
3. Substituting gives the profile criterion $\varphi(\omega) = \sum_i w_i\bigl(b_i - (v_i - v_{a(i)}) - \omega(u_i - u_{a(i)})\bigr)^2$, a quadratic in $\omega$, minimized at

$$\hat\omega \;=\; \frac{\sum_i w_i\,(u_i - u_{a(i)})\,\bigl(b_i - v_i + v_{a(i)}\bigr)}{\sum_i w_i\,(u_i - u_{a(i)})^2},$$

replaced by a user floor $\omega_{\min} > 0$ if smaller; then $\hat t_i = u_i + v_i/\hat\omega$.

Generic linear algebra would cost $O(n^3)$. For an unrooted tree, repeating the computation for a root on each branch (optimizing the root position on that branch) gives a rooting by the clock criterion in $O(n^2)$ time.

## Depends on

- [Weighted least-squares dating criterion](weighted-least-squares-dating-criterion.md)

## Expansion

Item 1 is $\partial\varphi/\partial t_i = 0$ rearranged; node $i$ appears in the terms of its own branch and of its two child branches. At a lowest internal node both children are tips, so item 1 gives $t_i$ affine in $t_{a(i)}$ and $1/\omega$. Inductively, if each child's date is affine in $t_i$ and $1/\omega$, item 1 can be solved for $t_i$ in terms of $t_{a(i)}$ and $1/\omega$; at the root no parent term remains, so $t_1 = u_1 + v_1/\omega$, and back-substitution propagates this form downward. Each step uses constant work per node, hence $O(n)$ overall. Because the dates are affine in $1/\omega$, each residual $b_i - \omega(t_i - t_{a(i)})$ is affine in $\omega$, which makes the profile quadratic. The quadratic's leading coefficient is positive exactly when not all tip dates are equal, the identifiability condition. The source writes the intermediate forms as its Equations (6) and (7) and proves optimality of the floor step in its online appendix. The same machinery, applied to trees with active precedence constraints collapsed, makes each active-set iteration of the constrained problem linear, so trees with more than 10,000 tips are dated easily.

## Sources

- T.-H. To, M. Jung, S. Lycett, O. Gascuel, "Fast dating using least-squares criteria and algorithms", *Systematic Biology* 65(1) (2016) 82–97, Sections "Linear Dating (LD) Algorithm, Without Constraints" (Equations (5)–(7)) and "Estimating the Root Position for Unrooted Trees" (Equation (9)), <https://doi.org/10.1093/sysbio/syv068> (PMC4678253).
