# Spreading speeds of the diffusive competitor–competitor–mutualist model

Consider two competitors $p_1, p_2$ and a mutualist $u$ of the first competitor:

$$
\begin{aligned}
\dot p_1 &= \alpha p_1 \Big(1 - p_1 - \frac{a p_2}{1 + m u}\Big) + D_1 p_{1,xx}, \\
\dot p_2 &= \beta p_2 (1 - p_2 - b p_1) + D_2 p_{2,xx}, \\
\dot u &= \gamma u \Big(1 - \frac{u}{L + l p_1}\Big) + D_3 u_{xx},
\end{aligned}
$$

with all parameters positive. The mutualist eases the competition that $p_2$ exerts on $p_1$ and has carrying capacity $L + l p_1$. Relevant equilibria are $E_4 = (0, 1, L)$, $E_6 = (1, 0, L + l)$ and a three-species coexistence state $E_7^+$.

**Theorem (mutualist helps the invader).** If $a < 1 + mL$, then $E_4$ is invadable by $p_1$. For $b < 1$ the invasion ends in coexistence $E_7^+$ with a single spreading speed equal to the speed of a travelling wave connecting $E_4$ to $E_7^+$; for $b \ge 1$ it ends in resident extinction $E_6$. In all cases the slowest spreading speed is at least

$$
c_1 = 2\sqrt{\alpha D_1 \Big(1 - \frac{a}{1 + mL}\Big)},
$$

and if $D_2 \le 2D_1$, $D_3 < 2D_1 + \frac{\gamma}{\alpha}\big(1 - \frac{a}{1+mL}\big)^{-1} D_1$ and, with

$$X = \alpha\Big(2 - \frac{D_2}{D_1}\Big)\Big(1 - \frac{a}{1+mL}\Big) + \beta, \qquad Y = \alpha\Big(2 - \frac{D_3}{D_1}\Big)\Big(1 - \frac{a}{1+mL}\Big) + \gamma,$$

the inequality

$$X \ge \frac{\beta\,ab}{1+mL} + \frac{\gamma\,aml}{(1+mL)^2}\,\frac{X}{Y}$$

holds (the source's (21) with its (19) substituted; equivalently $\frac{ab - (1+mL)}{(1+mL) - a} \le \frac{\alpha}{\beta}\big(2 - \frac{D_2}{D_1}\big) - \frac{\gamma}{\beta}\,\frac{aml}{(1+mL)((1+mL)-a)}\,\frac{X}{Y}$), then the system is linearly determinate with single spreading speed $c_1$. The source states this condition as its (18), whose last term it prints as $\frac{\gamma}{\beta}\frac{mal}{(1+mL)^2}\frac{X}{Y}$; that printed form is not equivalent to the one above, which is what substituting (19) into (21) gives, so the page states the latter.

**Theorem (mutualist helps the resident).** If $b < 1$, then $E_6$ is invadable by $p_2$. If either $ml \le (1+mL)(1-b)$ and $a \le 1 + mL$, or $ml > (1+mL)(1-b)$ and $a \le a_1$ with

$$
a_1 = \frac{1}{b^2}\Big( b(1+mL) + (2-b) ml - 2\sqrt{ml(1-b)\big(b(1+mL) + ml\big)} \Big),
$$

the invasion ends in coexistence $E_7^+$ with a single spreading speed; otherwise it ends in extinction of the resident $p_1$ (state $(0,1,L) = E_4$; the source's Theorem 3 prints "the resident extinction $E_6$", but $E_6 = (1,0,L+l)$ is the state the invasion starts from, and with $p_1$ extinct the mutualist settles at its own capacity $L$). In all cases the slowest spreading speed is at least $c_1 = 2\sqrt{\beta D_2 (1-b)}$; if $D_1 \le 2 D_2$ and $\frac{ab-1}{1-b} \le \frac{\beta}{\alpha}\big(2 - \frac{D_1}{D_2}\big)$, both competitors spread at this speed, and when the outcome is $E_7^+$ the system is linearly determinate.

## Depends on

- [Linear determinacy of spreading speeds in cooperative reaction–diffusion systems](linear-determinacy-of-spreading-speeds-in-cooperative-systems.md)

## Expansion

Substitutions such as $q_2 = 1 - p_2$ turn the system into a cooperative one with the source equilibrium at the origin, so the linear-determinacy theorem applies. The invader's linearized growth rate at the source gives $c_1$. Condition (II) becomes the stated diffusion inequalities, and condition (III) reduces to a componentwise inequality for the leading eigenvector, which is checked explicitly. In the mutualist-invader case a larger $L$ raises the speed toward $2\sqrt{\alpha D_1}$, erasing the effect of competition. In the mutualist-resident case, comparison with the $m = 0$ system shows that the mutualist cannot raise the invader's speed above the two-species Lotka–Volterra value.

## Sources

- Volodymyr Hrynkiv, Sergiy Koshkin, "Invasion waves in the presence of a mutualist", Mathematical Methods in the Applied Sciences 37 (2014), 2185–2197, <https://doi.org/10.1002/mma.2964>. Published version of arXiv:1705.05474, cited next; locators there refer to the arXiv version.
- Volodymyr Hrynkiv, Sergiy Koshkin, "Invasion waves in the presence of a mutualist", arXiv (2017). Theorem 1, Lemma 1, Theorem 2, Lemma 2, Lemma 3, Lemma 4, Theorem 3. <https://doi.org/10.48550/arXiv.1705.05474>
