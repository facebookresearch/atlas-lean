# Faltings height of an elliptic curve over its field of definition

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, let $E$ be an elliptic curve over
$L$, and let $\mathcal{E}$ be the
[Néron model of $E$ over $\mathcal{O}_L$](../../abelian-varieties/stable-faltings-height/neron-model-over-a-ring-of-integers.md),
with zero section $\varepsilon$. The invertible $\mathcal{O}_L$-module
$\omega = \varepsilon^* \Omega^1_{\mathcal{E}/\mathcal{O}_L}$ has
$\omega \otimes_{\mathcal{O}_L} L = H^0(E, \Omega^1_{E/L})$, and
$\omega \otimes_\sigma \mathbb{C} = H^0(E_\sigma, \Omega^1)$ for every embedding
$\sigma : L \to \mathbb{C}$, where $E_\sigma$ is the base change of $E$ along $\sigma$. With the
metrics

$$\| s \|_\sigma^2 = \frac{i}{2} \int_{E_\sigma(\mathbb{C})} s \wedge \bar s \qquad (s \in \omega \otimes_\sigma \mathbb{C}),$$

$\bar\omega = (\omega, (\| \cdot \|_\sigma)_\sigma)$ is a
[hermitian line bundle](../../arakelov-geometry/arithmetic-variety.md) on
$\operatorname{Spec} \mathcal{O}_L$, and the **Faltings height of $E/L$** is its normalized
[arithmetic degree](../../arakelov-geometry/arithmetic-intersection-numbers.md):

$$h_{\mathrm{Fal}}(E/L) = \frac{\widehat{\deg}(\bar\omega)}{[L : \mathbb{Q}]}
  = \frac{1}{[L : \mathbb{Q}]} \Bigl( \log \# \bigl( \omega / s \mathcal{O}_L \bigr)
  - \frac{1}{2} \sum_{\sigma : L \to \mathbb{C}} \log \Bigl( \frac{i}{2} \int_{E_\sigma(\mathbb{C})} s \wedge \bar s \Bigr) \Bigr)$$

for any nonzero $s \in \omega$; it does not depend on $s$, by the product formula. More generally, let
$n \ge 1$, give $\omega^{\otimes n}$ the metrics with $\| s^{\otimes n} \|_\sigma = \| s \|_\sigma^n$,
and let $t$ be a nonzero element of $(\omega \otimes_{\mathcal{O}_L} L)^{\otimes n}$. For a maximal
ideal $\mathfrak{p}$ of $\mathcal{O}_L$ let $\operatorname{ord}_\mathfrak{p}(t)$ be the integer $k$
such that $t$ generates $\mathfrak{p}^k \, (\omega^{\otimes n} \otimes_{\mathcal{O}_L} \mathcal{O}_{L,\mathfrak{p}})$;
it is $0$ for all but finitely many $\mathfrak{p}$. Then

$$n \, [L : \mathbb{Q}] \, h_{\mathrm{Fal}}(E/L) = \widehat{\deg}(\bar\omega^{\otimes n})
  = \sum_{\mathfrak{p}} \operatorname{ord}_\mathfrak{p}(t) \log \#(\mathcal{O}_L / \mathfrak{p})
  - \sum_{\sigma : L \to \mathbb{C}} \log \| t \|_\sigma .$$

The metric is Faltings' normalization, the one of the
[stable Faltings height](../../abelian-varieties/stable-faltings-height/faltings-height.md) in dimension one,
where $\frac{1}{2} |s \wedge \bar s| = \frac{i}{2} s \wedge \bar s$; but the height is computed with the
Néron model of $E$ over $L$ itself, with no extension of $L$, so it is not the stable height
(Silverman, Remark 1.2 (1)). Deligne's metric $\frac{1}{2\pi} \int |s \wedge \bar s|$ gives
$h_{\mathrm{Fal}}(E/L) + \frac{1}{2} \log \pi$.

## Depends on

- [Néron model of an abelian variety over the ring of integers of a number field](../../abelian-varieties/stable-faltings-height/neron-model-over-a-ring-of-integers.md),
  for $\mathcal{E}$ and the invertible module $\omega$ with its generic and complex fibres
- [Arithmetic varieties and hermitian vector bundles](../../arakelov-geometry/arithmetic-variety.md),
  for hermitian line bundles on $\operatorname{Spec} \mathcal{O}_L$
- [Arithmetic degree and arithmetic intersection numbers](../../arakelov-geometry/arithmetic-intersection-numbers.md),
  for $\widehat{\deg}$ on $\operatorname{Spec} \mathcal{O}_L$

## Proof depends on

- [Arithmetic degree and arithmetic intersection numbers](../../arakelov-geometry/arithmetic-intersection-numbers.md),
  for the class $\hat c_1(\bar\omega^{\otimes n}) = [(\operatorname{div}(t), -\log \| t \|^2)]$ of any
  nonzero rational section $t$, the additivity of $\hat c_1$ and $\widehat{\deg}$ under tensor
  products, and the vanishing of $\widehat{\deg}$ on principal arithmetic divisors
- [Principal Arakelov divisors have size one](../../arakelov-geometry/arakelov-divisors/size-principal.md),
  for the product formula behind the independence of $s$

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 255, "The height $h(E/K)$ is defined as
  $1/[K : \mathbb{Q}]$ times the degree of the metrized line bundle $\omega_{\mathcal{E}/R}$, where
  $\mathcal{E}/R$ is a Néron model for $E/K$", and the computation of the degree of
  $\omega^{\otimes 12}$ with a meromorphic section; p. 256, the archimedean contribution
  $\frac{n_v}{[K : \mathbb{Q}]} \log \bigl( \frac{i}{2} \int \alpha \wedge \bar\alpha \bigr)^{1/2}$,
  printed without the minus sign that the final contribution
  $-(n_v / 12 [K : \mathbb{Q}]) \log(|\Delta(\tau_v)| \operatorname{Im}(\tau_v)^6)$ on the same page
  carries; p. 254, Remark 1.2 (1), the height is not the stabilized height.
- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: §1.1, pp. 25–26, the degree
  $\deg \mathcal{L} = -\log \prod_v \| \ell \|_v$ of a line with absolute values, and
  $\#(L_{\mathcal{O}} / \mathcal{O} \ell) = \prod_{v \text{ finite}} \| \ell \|_v^{-1}$ for an
  $\mathcal{O}$-form; §1.2, p. 26, the metric $\frac{1}{(2\pi)^g} \int |\alpha \wedge \bar\alpha|$,
  with Faltings' $\frac{1}{2^g} |\alpha \wedge \bar\alpha|$; p. 27, $h(A) = \frac{1}{[k : \mathbb{Q}]} \deg \omega(A)$.
