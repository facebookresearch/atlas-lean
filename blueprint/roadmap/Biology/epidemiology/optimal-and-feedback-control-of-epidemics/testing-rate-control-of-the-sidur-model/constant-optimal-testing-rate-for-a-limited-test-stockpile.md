# Constant optimal testing rate for a limited test stockpile

**Setting.** Use the SIDUR model ([best-effort testing rate](best-effort-testing-rate-to-stop-epidemic-growth.md)) with constant infection rate $\beta$, recovery rate $\gamma$ and testing specificity $\theta$. A stockpile of $r_{\max}$ tests is used at a constant rate $C$ until it runs out:

$$
u(t) = \begin{cases} C, & 0 \le t \le T, \\ 0, & t > T, \end{cases} \qquad T := r_{\max}/C .
$$

Change to *infection time* $\xi(t) = \int_0^t x_I(\eta)\,d\eta$. Then exactly $x_S(\xi) = x_S^0 e^{-\beta\xi/N}$ and $x_U(\xi) = x_U^0 + \gamma\xi$. With the approximation $x_T\approx(1-\theta)N$,

$$
x_I(\xi) = x_I^0 + x_S^0\bigl(1 - e^{-\beta\xi/N}\bigr) - \gamma\xi - \int_0^\xi \frac{u(\eta)}{(1-\theta)N}\,d\eta .
$$

Let $\Xi$ be the infection-time value at which the stockpile is exhausted, defined implicitly by

$$
\int_0^{\Xi} \frac{d\xi}{x_I^0 + x_S^0\bigl(1 - e^{-\beta\xi/N}\bigr) - \frac{C\xi}{(1-\theta)N} - \gamma\xi} = T ,
$$

and define the testing-phase and free-phase reproduction numbers

$$
R_1 = \frac{x_S^0\beta}{\frac{C}{1-\theta} + \gamma N}, \qquad R_2 = \frac{x_S^0\beta}{\gamma N}, \qquad R_2 > R_1 .
$$

**Proposition (COST policy).** Let $\xi_{p_1} = \tfrac{N}{\beta}\ln R_1$ and $\xi_{p_2} = \tfrac{N}{\beta}\ln R_2$, and assume $R_1>1$ and $\xi_{p_1}<\Xi$, so that both peaks exist ($R_1>1$ alone does not give this: a small stockpile makes $\Xi\to0$). The epidemic then has a peak during testing at $\xi_{p_1}$ and a second peak after the stockpile runs out at $\xi_{p_2}$, with $\Xi\le\xi_{p_2}$. Their heights are

$$
\begin{aligned}
x_I^{p_1} &= x_I^0 + x_S^0\Bigl(1 - \frac{1}{R_1}\Bigr) - x_S^0\,\frac{\ln R_1}{R_1}, \\
x_I^{p_2} &= x_I^0 + x_S^0\Bigl(1 - \frac{1}{R_2}\Bigr) - x_S^0\,\frac{\ln R_2}{R_2} - \frac{C\,\Xi}{(1-\theta)N}.
\end{aligned}
$$

The constant rate $C$ that minimises $\max\{x_I^{p_1},x_I^{p_2}\}$ makes the two peaks equal. It is the solution of the implicit exhaustion equation above together with the optimality condition

$$
\Xi = \frac{N}{\beta}\left(1 + \ln R_1 - \frac{R_1}{R_2 - R_1}\ln\frac{R_2}{R_1}\right),
$$

and this solution is unique under these assumptions.

## Depends on

- [Best-effort testing rate to stop epidemic growth](best-effort-testing-rate-to-stop-epidemic-growth.md)

## Expansion

In infection time the susceptible equation is linear, which gives the closed forms above. The peaks are the zeros of $dx_I/d\xi$, i.e. $x_S^0\tfrac{\beta}{N}e^{-\beta\xi/N} = \tfrac{C}{(1-\theta)N} + \gamma$ during testing and $=\gamma$ afterwards. Substituting $e^{-\beta\xi_{p_i}/N} = 1/R_i$ gives the peak heights. Raising $C$ lowers the first peak, while for reasonably large $C$ the cumulative depletion term $C\,\Xi$ decreases ($\tfrac{d(C\Xi)}{dC} = \int_0^T [x_I(\tau)-x_I(T)]\,d\tau$), so the second peak rises. The maximum of a decreasing and an increasing function is minimised where they cross. Equating the two heights and using $\tfrac{C}{(1-\theta)N} = \tfrac{x_S^0\beta}{N}\bigl(\tfrac{1}{R_1} - \tfrac{1}{R_2}\bigr)$ gives the optimality condition. Testing too hard exhausts the stockpile early and causes a large second wave; testing too little fails to flatten the first.

## Sources

- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, Liudmila Tumash, Pierre-Alexandre Bliman, "Effective Testing Policies for Controlling an Epidemic Outbreak", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 2806–2811, <https://doi.org/10.1109/cdc45484.2021.9683300>. Published version of arXiv:2109.12553, cited next; locators there refer to the arXiv version.
- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, Liudmila Tumash, Pierre-Alexandre Bliman, "Effective Testing Policies for Controlling an Epidemic Outbreak", arXiv 2021: Proposition 1, Proposition 2, Section 4, Proposition 4. The paper's displayed first-peak formula writes the last term as $x_S^0 R_1\ln R_1$. Substituting $\xi_{p_1}$ into Proposition 2 gives $x_S^0(\ln R_1)/R_1$, which is the form that reproduces the paper's optimality condition. <https://doi.org/10.48550/arXiv.2109.12553>
