# Stable Faltings height

Let $K$ be a number field and $A$ an abelian variety of dimension
$g$ over $K$. Choose a finite extension $L/K$ over which $A$ has semi-abelian reduction at every
finite place, a semi-abelian model $\pi : \mathcal{A} \to \operatorname{Spec} \mathcal{O}_L$ of
$A_L$ (a smooth separated commutative group scheme of finite type with generic fibre $A_L$ whose
fibres are extensions of abelian varieties by tori), and its zero section $\varepsilon$. The
invertible $\mathcal{O}_L$-module $\omega = \varepsilon^* \Omega^g_{\mathcal{A}/\mathcal{O}_L}$
satisfies $\omega \otimes_{\sigma} \mathbb{C} = H^0(A_\sigma, \Omega^g)$ for every embedding
$\sigma : L \to \mathbb{C}$; give it the metrics

$$\|s\|_\sigma^2 = \frac{1}{2^g} \int_{A_\sigma(\mathbb{C})} \left| s \wedge \bar s \right|,$$

where $\left| s \wedge \bar s \right| = i^{g^2} s \wedge \bar s$ is the associated positive volume
form. Then

$$h_F(A) = \frac{1}{[L : \mathbb{Q}]} \Bigl( \log \# \bigl( \omega / s \mathcal{O}_L \bigr)
  - \sum_{\sigma : L \to \mathbb{C}} \log \|s\|_\sigma \Bigr)$$

for any nonzero $s \in \omega$, the normalized Arakelov degree of $\omega$ with these metrics.
It does not depend on $L$, on the model or on $s$.

This is Faltings' original normalization, as described by Gaudron and Rémond, *Théorème des
périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), §2.3, pp. 351–352
(<https://doi.org/10.4171/CMH/322>). Their Définition 2.1 uses instead the height $h(A)$ defined
with $(2\pi)^g$ in place of $2^g$ in the metric, so that $h_F(A) = h(A) - \frac{g}{2} \log \pi$.
Reference: G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent.
Math. 73 (1983), 349–366, <https://doi.org/10.1007/BF01388432>.
