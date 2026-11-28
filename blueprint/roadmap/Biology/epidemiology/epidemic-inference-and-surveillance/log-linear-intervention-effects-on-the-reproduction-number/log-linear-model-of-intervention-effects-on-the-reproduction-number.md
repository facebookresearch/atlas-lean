# Log-linear model of intervention effects on the reproduction number

**Setting.** For countries $c$, days $t$ and interventions $i = 1, \dots, I$, let $x_{i,t,c} \in \{0, 1\}$ indicate that intervention $i$ is active. The reproduction number is

$$R_{t,c} = R_{0,c}\prod_{i=1}^{I} \exp(-\alpha_{i,c}\, x_{i,t,c}), \qquad \alpha_{i,c} = \alpha_i + z_{i,c}, \quad z_{i,c} \sim \mathcal{N}(0, \sigma_i^2),$$

where $R_{0,c} > 0$ absorbs all time-invariant country factors, $\alpha_i$ is the mean effect of intervention $i$ and $\sigma_i^2$ its cross-country variance (partial pooling). The *effectiveness* of intervention $i$ in a country with effect $\alpha_{i,c}$ is $e_{i,c} = 1 - \exp(-\alpha_{i,c})$, the fractional reduction of $R_{t,c}$ it causes. $R_{t,c}$ is linked to daily infection growth through a gamma generation-interval distribution, and infections to reported cases and deaths through delay distributions and negative binomial observation noise.

**Proposition.**

1. $\log R_{t,c} = \log R_{0,c} - \sum_i \alpha_{i,c}\, x_{i,t,c}$ is linear in the indicators, so the relative change in $R_{t,c}$ from switching on intervention $i$ is $e_{i,c}$, independent of $R_{0,c}$ and of the other active interventions; the absolute reduction $e_{i,c} R_{t,c}$ is proportional to the current $R_{t,c}$.
2. (Combination) A set $A$ of interventions has joint effectiveness

$$e_{A,c} = 1 - \prod_{i \in A} (1 - e_{i,c}) = 1 - \exp\Bigl(-\sum_{i \in A}\alpha_{i,c}\Bigr),$$

which satisfies $\max_{i \in A} e_{i,c} \le e_{A,c} \le \sum_{i \in A} e_{i,c}$ when all $\alpha_{i,c} \ge 0$.
3. (Control threshold) With the set $A$ active, $R_{t,c} < 1$ if and only if $\sum_{i \in A}\alpha_{i,c} > \log R_{0,c}$.
4. (Pooled effectiveness) Over the cross-country distribution $\alpha_i + z$, $z \sim \mathcal{N}(0, \sigma_i^2)$, the median effectiveness is $1 - e^{-\alpha_i}$, while the mean effectiveness $1 - e^{-\alpha_i + \sigma_i^2/2}$ is smaller.
5. (Growth rate) With a gamma generation interval of shape $a > 0$ and rate $b > 0$, the epidemic growth rate is $r_{t,c} = b\,(R_{t,c}^{1/a} - 1)$, so switching on intervention $i$ multiplies $1 + r/b$ by $e^{-\alpha_{i,c}/a}$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)
- [Gamma generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number-gamma-measure.md)

## Expansion

(1)–(3) are algebra on the exponential form; the bounds in (2) are $1 - \prod(1 - e_i) \ge \max e_i$ and the union bound $1 - \prod (1 - e_i) \le \sum e_i$ for $e_i \in [0,1]$. (4): $1 - e^{-(\alpha + z)}$ is an increasing function of the symmetric normal variable $z$, so its median is attained at $z = 0$; its mean uses $\mathbb{E}\, e^{-z} = e^{\sigma^2/2}$. (5) inverts the Euler–Lotka relation $R = (1 + r/b)^a$ for a gamma interval. The multiplicative form encodes the assumption that an intervention removes a fixed fraction of remaining transmission. The source fitted the model to 41 countries (January to May 2020) and grouped effects as small, moderate or large for reductions below $17.5\%$, between $17.5\%$ and $35\%$, and above $35\%$; closing both schools and universities and limiting gatherings to at most $10$ people were in the large category in most of $206$ sensitivity analyses. Because interventions were often introduced close together, effects are only weakly identified individually, which is why the authors emphasize robustness across modelling choices over point estimates.

## Sources

- J. M. Brauner, S. Mindermann, M. Sharma, D. Johnston, J. Salvatier, T. Gavenčiak, et al., "Inferring the effectiveness of government interventions against COVID-19", Science 371 (2021) eabd9338, Materials and methods, "Model", <https://doi.org/10.1126/science.abd9338> (PMC7877495).
