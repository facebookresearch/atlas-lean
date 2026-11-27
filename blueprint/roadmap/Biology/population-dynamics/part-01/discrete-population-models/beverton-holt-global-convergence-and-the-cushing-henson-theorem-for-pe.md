# Beverton–Holt dynamics and the Cushing–Henson conjectures

For the Beverton–Holt equation $x_{n+1} = \mu K x_n/(K + (\mu - 1) x_n)$ with $\mu > 1$ and $K > 0$, the substitution $y_n = 1/x_n$ gives the affine recursion $y_{n+1} = q y_n + (1 - q)/K$ with $q = 1/\mu \in (0, 1)$, so $y_n \to 1/K$ and $x_n \to K$ for every $x_0 > 0$. In a periodically varying environment, $x_{n+1} = \mu K_n x_n/(K_n + (\mu - 1) x_n)$ with $\mu > 1$ and a non-constant sequence $K_n > 0$ with $K_{n+p} = K_n$ for some $p \ge 2$, Cushing and Henson conjectured (Stević 2006, Conjectures 1.1 and 1.2) that (1) there is a positive $p$-periodic solution $\bar x_0, \dots, \bar x_{p-1}$ that globally attracts all positive solutions, and (2) $\frac1p\sum_{i=0}^{p-1}\bar x_i < \frac1p\sum_{i=0}^{p-1} K_i$: a periodic environment is deleterious. Both hold. With $y_n = 1/x_n$ and $L_n = 1/K_n$ the equation becomes $y_{n+1} = q y_n + (1 - q) L_n$ (Stević, eq. (1.2)), whose unique $p$-periodic solution is given in closed form by eqs. (1.4)–(1.6), every solution satisfies $y_{mp+i} = q^p y_{(m-1)p+i} + c_i$ (Remark 1.4, eq. (1.10)), so it converges to the periodic one, and Theorem 1.3 proves the strict inequality between the averages. The conjectures were first confirmed by Elaydi and Sacker, as reported by Stević and by Kon (2004), who extends the second to a class of models $x_{n+1} = g(x_n/K_n)\, x_n$.

## Expansion

1. The autonomous map, its conjugacy to an affine map and global convergence.
2. The periodic equation, the closed form of its $p$-periodic solution through $y = 1/x$, and global attraction from the recursion over one period.
3. The strict inequality between the averages (Theorem 1.3 of Stević), and its extension to concave growth functions $g$ (Kon 2004).
4. Variants with periodic $\mu_n$ (Stević, Remark 1.6), as separate statements.

## Sources

- S. Stević, A short proof of the Cushing–Henson conjecture, Discrete Dyn. Nat. Soc. 2006 (2006), 37264, Conjectures 1.1–1.2, eqs. (1.2)–(1.6), Theorem 1.3, Remarks 1.4–1.6. <https://doi.org/10.1155/ddns/2006/37264>
- R. Kon, A note on attenuant cycles of population models with periodic carrying capacity, J. Difference Equ. Appl. 10 (2004), 791–793. <https://doi.org/10.1080/10236190410001703949>
- Original result: J. M. Cushing and S. M. Henson, A periodically forced Beverton–Holt equation, J. Difference Equ. Appl. 8 (2002), 1119–1120. <https://doi.org/10.1080/1023619021000053980> The two conjectures follow their statement in Stević (2006).
- Original result: S. Elaydi and R. J. Sacker, Nonautonomous Beverton–Holt equations and the Cushing–Henson conjectures, J. Difference Equ. Appl. 11 (2005), 337–346. <https://doi.org/10.1080/10236190412331335418> The first confirmation of both conjectures follows Stević (2006) and Kon (2004).
- M. Bohner and H. Warth, The Beverton–Holt dynamic equation, Applicable Analysis 86 (2007), 1007–1015, Sections 1–2.
