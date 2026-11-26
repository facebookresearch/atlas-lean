# Brière and quadratic thermal performance curves

**Setting.** For constants $q > 0$ and $0 \le T_{\min} < T_{\max}$ (temperatures in °C), the *Brière* and *quadratic* thermal performance curves are

$$B(T) = q\,T\,(T - T_{\min})\sqrt{T_{\max} - T}, \qquad Q(T) = -q\,(T - T_{\min})(T - T_{\max}),$$

for $T_{\min} \le T \le T_{\max}$, and $0$ outside $[T_{\min}, T_{\max}]$. Rate traits (development rates, biting rate, fecundity, parasite development rate) are fitted with $B$; probability traits (survival, vector competence) and lifespan with $Q$, truncated at $1$ where needed.

**Proposition.**

1. $Q$ is concave on $[T_{\min}, T_{\max}]$, symmetric about $(T_{\min} + T_{\max})/2$, and maximal there with $Q_{\max} = q (T_{\max} - T_{\min})^2/4$.
2. $B$ has a unique maximum on $(T_{\min}, T_{\max})$, at

$$T^\ast = \frac{4T_{\max} + 3T_{\min} + \sqrt{16T_{\max}^2 - 16T_{\min}T_{\max} + 9T_{\min}^2}}{10},$$

and $T^\ast > (T_{\min} + T_{\max})/2$: Brière curves are left-skewed, rising slowly and collapsing quickly above the optimum. For $T_{\min} = 0$, $T^\ast = 0.8\,T_{\max}$.
3. (Thermal limits of a product) If $R_0(T)$ is a positive power of a product of such curves (divided by positive functions such as a mortality rate), then $R_0(T) > 0$ exactly on the intersection of the open supports, so the lower thermal limit of transmission is the largest trait lower limit and the upper limit the smallest trait upper limit.
4. (Jensen effect) If temperature fluctuates with mean $\bar T$ inside an interval on which a curve is concave, the mean performance is at most the performance at $\bar T$; in particular fluctuations around the optimum of $Q$ always lower mean performance.

## Expansion

(1) is elementary. (2): on the open interval, $(\log B)' = 1/T + 1/(T - T_{\min}) - 1/(2(T_{\max} - T))$; clearing denominators gives $5T^2 - (4T_{\max} + 3T_{\min})T + 2T_{\min}T_{\max} = 0$. This quadratic is $\le 0$ at $T_{\min}$ (value $2T_{\min}(T_{\min} - T_{\max})$) and $> 0$ at $T_{\max}$ (value $T_{\max}(T_{\max} - T_{\min})$), so exactly one root, the larger, lies in $[T_{\min}, T_{\max})$, and it is the maximizer. At the midpoint $m$, $(\log B)'(m) = 1/m + 1/(T_{\max} - T_{\min}) > 0$, so $T^\ast > m$. (3): a product vanishes where any factor does. (4) is Jensen's inequality. Across 16 vector–pathogen systems the source found every temperature-dependent $R_0$ to be unimodal, with optima between about $23$ and $29$ °C; rate traits had asymmetric responses with higher optima and probability traits more symmetric responses with lower optima, so mortality typically sets the upper limit and development the lower one. Because the curves are fitted at constant laboratory temperatures, the Jensen effect is one reason field transmission can depart from the constant-temperature $R_0(T)$.

## Sources

- E. A. Mordecai, J. M. Caldwell, M. K. Grossman, C. A. Lippi, L. R. Johnson, M. Neira, et al., "Thermal biology of mosquito-borne disease", Ecology Letters 22 (2019) 1690–1708, Eqs. (1)–(3), "Limitations to the $R_0(T)$ approach" and results on trait thermal responses, <https://doi.org/10.1111/ele.13335> (PMC6744319).
- J.-F. Brière, P. Pracros, A.-Y. Le Roux, J.-S. Pierre, "A novel rate model of temperature-dependent development for arthropods", Environmental Entomology 28 (1999) 22–29, <https://doi.org/10.1093/ee/28.1.22>.
