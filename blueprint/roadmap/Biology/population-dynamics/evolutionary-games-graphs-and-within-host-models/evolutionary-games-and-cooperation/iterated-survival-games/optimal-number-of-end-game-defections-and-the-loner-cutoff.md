# Optimal number of end-game defections and the loner cutoff

Use the [iterated survival game](survival-probability-of-switching-strategies-in-the-iterated-survival-game.md) with strategies $S_j$ (defect in the last $j$ of $n$ steps) and payoffs $A(S_j;S_i)$. Assume each step is a classical Prisoner's Dilemma in survival probabilities,

$$c > a > d > b, \qquad a > \tfrac{b+c}{2}\ \ (\text{so } a^2 > bc).$$

**Gain from defecting against a cooperator.**

$$A(S_j;S_0)-A(S_0;S_0) = a^{2n}\left[\frac{a_0-c}{a_0-bc}\Big(\frac{bc}{a^2}\Big)^{j}+\Big(\frac{c(1-b)}{a_0-bc}-\frac{a(1-a)}{a_0-a^2}\Big)\Big(\frac{a_0}{a^2}\Big)^{j}-\frac{a_0-a}{a_0-a^2}\right],$$

with $A(S_1;S_0)-A(S_0;S_0) = a^{2(n-1)}(c-a) > 0$, so one final defection is always favoured. As a function of real $j \ge 0$ its slope changes sign at most once.

**Optimal switch point.** When it exists, the interior maximizer is

$$j_{\mathrm{opt}} = \frac{\ln\!\left[\Big(\dfrac{a(1-a)(a_0-bc)}{(a_0-c)(a_0-a^2)}-\dfrac{c(1-b)}{a_0-c}\Big)\dfrac{\ln(a_0/a^2)}{\ln(bc/a^2)}\right]}{\ln(bc/a_0)},$$

and the optimal integer number of defections $J_{\mathrm{opt}}$ is $\lfloor j_{\mathrm{opt}}\rfloor$ or $\lceil j_{\mathrm{opt}}\rceil$. If $n > j_{\mathrm{opt}}$ then $S_{J_{\mathrm{opt}}}$ is the best reply to $S_0$ regardless of $n$; if $n \le j_{\mathrm{opt}}$ the best reply is $S_n$.

**Theorem (loner cutoff).** Define

$$a_0^{*} = \frac{c-a}{c-a+a^2-bc}\,a^2+\frac{a^2-bc}{c-a+a^2-bc}\,a ,$$

a weighted average lying strictly between $a^2$ and $a$. If $a_0 < a_0^{*}$, a finite optimum $J_{\mathrm{opt}}$ exists, with $J_{\mathrm{opt}}\to 1$ as $a_0 \to 0$, $J_{\mathrm{opt}} \to \infty$ as $a_0 \uparrow a_0^{*}$, and $J_{\mathrm{opt}}$ increasing in $a_0$. If $a_0 \ge a_0^{*}$, the payoff keeps increasing in $j$, so full defection $S_n$ is the best reply to $S_0$ for every $n$.

## Depends on

- [Survival probability of switching strategies in the iterated survival game](survival-probability-of-switching-strategies-in-the-iterated-survival-game.md)

## Proof sketch

The bracket is $\alpha x^j + \beta y^j - \gamma$ with $x = bc/a^2 < 1$, $y = a_0/a^2$, $\alpha = (a_0-c)/(a_0-bc)$ and $\beta$ the middle coefficient; a sum of two exponentials has at most one critical point, and setting the derivative to zero gives $(x/y)^j = -\beta\ln y/(\alpha\ln x)$, which is $j_{\mathrm{opt}}$. If $a_0 < a^2$ both exponentials decay, the gain tends to $-a^{2n}(a_0-a)/(a_0-a^2) < 0$, so after the initial rise it must peak and fall: too many defections leave the defector alone too long. If $a_0 > a^2$ the $y^j$ term dominates for large $j$, and the gain grows without bound in the bracket exactly when $\beta > 0$. Solving $\beta = 0$, that is $c(1-b)(a_0-a^2) = a(1-a)(a_0-bc)$, gives $a_0 = ac(a-b)/(c-a+a^2-bc) = a_0^{*}$. The weights $c-a$ (individual gain from defecting) and $a^2-bc$ (loss in pair survival) explain the cutoff: a large pair-survival cost pushes $a_0^{*}$ toward $a$ and supports cooperation even when loners fare fairly well. The case $a_0 = a^2$ needs the non-geometric form of the sums but also has a finite optimum. Even in very long games $J_{\mathrm{opt}}$ is typically small, so cooperation is sustained for most of the game when lone individuals have bleak prospects.

## Sources

- O. Salagnac and J. Wakeley, "The consequences of switching strategies in a two-player iterated survival game", Journal of Mathematical Biology 82 (2021), Sect. 3, Eqs. (15)–(26) and Appendix 1, <https://doi.org/10.1007/s00285-021-01569-3>, PMCID PMC7867574.
