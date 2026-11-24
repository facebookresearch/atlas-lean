# Directional selection differential

For a fitness function $W : \mathbb{R} \to \mathbb{R}$, a trait mean $\mu$ and a variance $v \ge 0$, the directional selection differential is

$$S = \frac{\int (z - \mu)\, W(z) \, dN(\mu, v)(z)}{\bar w(\mu)},$$

where $\bar w$ is the [mean fitness](mean-fitness.md), with the convention $x/0 = 0$. For nonnegative $W$ with $W$ and $z \mapsto (z - \mu) W(z)$ integrable with respect to $N(\mu, v)$ and $\bar w(\mu) > 0$, it is the fitness-weighted mean trait of the selected parents minus the mean $\mu$ before selection.
