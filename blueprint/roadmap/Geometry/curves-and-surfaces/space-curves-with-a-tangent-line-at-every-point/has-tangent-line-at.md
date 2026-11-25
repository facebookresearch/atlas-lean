# Oriented tangent line to a space curve

A curve $\gamma \colon \mathbb{R} \to \mathbb{R}^3$ has an oriented tangent line at $t$ if there is a unit vector $v$
such that for every $\varepsilon > 0$ there is $\delta > 0$ with

$$
\bigl\| (\gamma(s) - \gamma(t)) - \operatorname{sign}(s - t)\, \|\gamma(s) - \gamma(t)\|\, v \bigr\| \le \varepsilon\, \|\gamma(s) - \gamma(t)\|
\quad \text{whenever } 0 < |s - t| < \delta:
$$

along the nonzero secants, the secant directions $(\gamma(s) - \gamma(t))/\|\gamma(s) - \gamma(t)\|$ tend to $v$ from the
right and to $-v$ from the left; parameters $s$ with $\gamma(s) = \gamma(t)$ impose no condition. No periodicity,
continuity or injectivity is assumed here; those hypotheses belong to the statement of Fréchet's problem.
