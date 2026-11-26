# Speed of adaptation from a marked lineage trajectory

Consider a large asexual population in which a marked lineage (for example all cells carrying a given beneficial mutation, detectable by a phenotype such as sterility) has frequency $f(t) \in (0,1)$ and constant Malthusian fitness $w_S$, while the rest of the population has mean fitness $\bar w_R(t)$, which increases as new mutations arise and spread. In the deterministic continuous-time limit the log-odds $y = \ln\frac{f}{1-f}$ satisfies

$$\frac{dy}{dt} = w_S - \bar w_R(t).$$

Let $\tau_{\mathrm{up}} < \tau_{\mathrm{down}}$ be the times when the marker first rises above and finally falls below a detection frequency $f_0$, with log-odds slopes $s_{\mathrm{up}} = y'(\tau_{\mathrm{up}}) > 0$ and $s_{\mathrm{down}} = -y'(\tau_{\mathrm{down}}) > 0$, and $\tau_{\mathrm{transit}} = \tau_{\mathrm{down}} - \tau_{\mathrm{up}}$. Then:

1. $s_{\mathrm{up}}$ is the fitness lead of the lineage over the rest of the population at $\tau_{\mathrm{up}}$, $s_{\mathrm{down}}$ its lag at $\tau_{\mathrm{down}}$, and the maximum frequency is reached when $\bar w_R(t) = w_S$.
2. The average speed of mean-fitness increase over the transit is

$$\frac{\bar w_R(\tau_{\mathrm{down}}) - \bar w_R(\tau_{\mathrm{up}})}{\tau_{\mathrm{transit}}} = \frac{s_{\mathrm{up}} + s_{\mathrm{down}}}{\tau_{\mathrm{transit}}}.$$

3. If $\bar w_R$ increases at constant speed $v$, then $y$ is a downward parabola, $s_{\mathrm{up}} = s_{\mathrm{down}}$, and the maximum lies at the midpoint of $[\tau_{\mathrm{up}}, \tau_{\mathrm{down}}]$; $s_{\mathrm{down}} > s_{\mathrm{up}}$ indicates that adaptation accelerated during the transit and $s_{\mathrm{down}} < s_{\mathrm{up}}$ that it slowed.

The initial slope $s_{\mathrm{up}}$ thus measures where in the standing fitness distribution the mutation arose rather than its own effect: a mutation of effect $s$ spreads at rate $s_{\mathrm{up}} > s$ when it occurred in an already-fit background. Selective sweeps and clonal interference are the two outcomes of the same comparison between the lineage's fitness and the rising population mean.

## Depends on

- [Clonal interference](clonal-interference.md)

## Expansion

Writing $f' = f(w_S - \bar w)$ and $\bar w = f w_S + (1-f)\bar w_R$ gives $f' = f(1-f)(w_S - \bar w_R)$, hence $y' = f'/(f(1-f)) = w_S - \bar w_R$. Item 1 is this identity at the three times. Item 2 follows by subtracting $y'(\tau_{\mathrm{up}}) = w_S - \bar w_R(\tau_{\mathrm{up}})$ and $y'(\tau_{\mathrm{down}}) = w_S - \bar w_R(\tau_{\mathrm{down}})$, which eliminates the unknown $w_S$. If $\bar w_R(t) = \bar w_R(\tau_{\mathrm{up}}) + v(t - \tau_{\mathrm{up}})$, then $y'' = -v$ and $y(\tau_{\mathrm{up}}) = y(\tau_{\mathrm{down}}) = \ln\frac{f_0}{1-f_0}$, so the parabola is symmetric about the midpoint. By Fisher's fundamental theorem $v$ equals the variance in fitness, so asymmetry of a trajectory reveals fluctuations of the standing genetic variance. In experimental yeast populations, trajectories of sterile mutations gave mean fitness increasing by about $1\%$ per 100 generations, consistent with direct competitive fitness assays.

## Sources

- G. I. Lang, D. Botstein and M. M. Desai, "Genetic variation and the fate of beneficial mutations in asexual populations", Genetics (2011), sections "Parameterization of mutational trajectories", "A new take on clonal interference" and "The tempo of adaptation", <https://doi.org/10.1534/genetics.111.128942>, PMCID: PMC3176544.
