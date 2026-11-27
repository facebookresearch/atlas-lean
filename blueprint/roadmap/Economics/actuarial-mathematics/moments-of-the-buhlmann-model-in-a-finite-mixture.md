# Moment identities of the Bühlmann model in a finite latent mixture

Let $\Theta$ have a finite law, and given $\Theta = \theta$ let $X_1, \dots, X_n$ ($n \ge 1$) be conditionally i.i.d. with finitely many real values, conditional mean $m(\theta)$ and conditional variance $v(\theta)$, the joint law being the mixture over $\theta$ of the product laws. With $\bar X = n^{-1}\sum_i X_i$, $a = \operatorname{Var}(m(\Theta))$ and $\bar v = E[v(\Theta)]$, one has $\operatorname{Cov}(m(\Theta), \bar X) = a$ and $\operatorname{Var}(\bar X) = a + \bar v/n$. The best affine predictor of $m(\Theta)$ from $\bar X$, with credibility weight $a/(a + \bar v/n)$ when $a + \bar v/n > 0$, and its optimality are separate statements; it is not the posterior mean in general.

## Sources

- Lecture notes *Bühlmann Model*, ACT 4630, University of Manitoba, Winter 2017, section "Derivation of the Credibility factor in Bühlmann Model", <https://home.cc.umanitoba.ca/~farhadi/ACT4630Winter2017/Buhlmann.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
