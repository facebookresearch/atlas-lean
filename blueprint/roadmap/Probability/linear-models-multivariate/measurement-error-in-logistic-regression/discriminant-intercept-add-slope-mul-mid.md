# Logistic discriminant lines pass through the prior log odds at the midpoint

For real numbers $p$, $\mu_0$, $\mu_1$ and $v$, let $\beta = (\mu_1 - \mu_0)/v$ and $\alpha = \log\frac{p}{1-p} - \beta\frac{\mu_0 + \mu_1}{2}$, where real division uses $x/0 = 0$ (so $\beta = 0$ when $v = 0$) and $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. Then the line $\alpha + \beta x$ takes the value $\log\frac{p}{1-p}$ at $x = (\mu_0 + \mu_1)/2$. For a prior $0 < p < 1$ this value is the prior log odds.
