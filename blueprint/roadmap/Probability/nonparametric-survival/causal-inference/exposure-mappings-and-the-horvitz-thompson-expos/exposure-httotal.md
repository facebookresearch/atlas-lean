# Exposure HTTotal

Let $U$ be a finite set of $N$ units, $\Omega$ a set of assignments, $e : U \times \Omega \to \Delta$ an exposure mapping, $p$ a probability mass function (design) on $\Omega$, and $y^r : U \times \Omega \to \mathbb R$ randomization potential outcomes, so $y^r_i(z)$ is the observed outcome of unit $i$ at the realized assignment $z$. Let $\pi_i(d) = p(\{z : e_i(z) = d\})$ be the exposure probabilities. For an exposure $d$ and an assignment $z$, the Horvitz–Thompson exposure-total estimator (Aronow and Samii (2017), estimator (1), $\hat y^T_{HT}(d)$, which estimates the total $y^T(d)$) is

$$\hat y^T_{HT}(d)(z) = \sum_{i \in U :\, e_i(z) = d} \frac{y^r_i(z)}{\pi_i(d)},$$

with the convention $y / 0 = 0$. Dividing by $N$ gives the estimator of the mean $\mu(d)$.
