# Stochastic movement of infectives on a travel network

Let cities $1, \dots, K$ each carry the
[chain-binomial SEIR step](chain-binomial-seir-step-with-poisson-transmission.md), and let
$P_t = (p_{ij}(t))$ be a row-stochastic origin-destination matrix for day $t$, with $p_{ij}(t)$ the
proportion of people in city $i$ who are in city $j$ at the end of the day (so $p_{ii}(t)$ is the
proportion who stay). After the within-city step, each of the $I_i$ infectives of city $i$ is
assigned to destinations by independent Bernoulli trials,
$B_{mj} \sim \mathrm{Bernoulli}(p_{ij}(t))$ for $m = 1, \dots, I_i$ and every $j$ (including $j = i$),
giving raw counts $\tilde M_{ij} = \sum_m B_{mj}$. These are rescaled to conserve infectives,

$$M_{ij} \;=\; I_i\, \frac{\tilde M_{ij}}{\sum_{l} \tilde M_{il}} \quad (\text{rounded}), \qquad
I_j' \;=\; \sum_{i=1}^K M_{ij},$$

so that $\sum_j M_{ij} = I_i$: movement redistributes infectives without creating or destroying
them, and $\mathbb{E}[\tilde M_{ij}] = I_i\, p_{ij}(t)$. Travel restrictions are modelled by
replacing baseline flows with reduced ones, which lowers the off-diagonal $p_{ij}(t)$ and raises
$p_{ii}(t)$.

## Depends on

- [Chain-binomial SEIR step with Poisson transmission](chain-binomial-seir-step-with-poisson-transmission.md)

## Expansion

Independent Bernoulli trials per destination do not by themselves place each person in exactly one
city, so the raw totals $\sum_j \tilde M_{ij}$ fluctuate around $I_i$; the rescaling keeps the
randomness in the relative allocation while preserving the patch total, and because stayers are
drawn the same way as movers it introduces no bias in the relative pattern. The resulting model is a
discrete-time stochastic metapopulation SEIR process: within-patch transmission is local, and
coupling between patches arises only through the movement of infectives. Repeated simulation
(1000 runs) propagates demographic noise in infection, recovery and movement into the predicted
case counts under each intervention scenario.

## Sources

- S. Lai, N. W. Ruktanonchai, L. Zhou et al., "Effect of non-pharmaceutical interventions to contain COVID-19 in China", *Nature* 585 (2020), <https://doi.org/10.1038/s41586-020-2293-x> (PMC7116778), Methods, "Data analysis", subsection "Movement".
