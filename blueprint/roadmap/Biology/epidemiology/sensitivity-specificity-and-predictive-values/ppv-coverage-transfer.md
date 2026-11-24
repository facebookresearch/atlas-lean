# Coverage of a joint confidence set transfers to the PPV

Let $\mu$ be a probability measure on $\Omega$, let
$\theta(\omega) = (\pi, \mathrm{se}, \mathrm{sp})$ be the true diagnostic parameters,
$S(\omega) \subseteq \mathbb{R}^3$ a joint confidence set for them and
$T(\omega) \subseteq \mathbb{R}$ an output set for the [positive predictive value](ppv.md), for
$\omega \in \Omega$. Assume that

- the coverage events $\{\omega : \theta(\omega) \in S(\omega)\}$ and
  $\{\omega : \mathrm{PPV}(\theta(\omega)) \in T(\omega)\}$ are measurable;
- for every $\omega$, $T(\omega)$ contains the PPV image of $S(\omega)$:
  $\mathrm{PPV}(x) \in T(\omega)$ for every $x \in S(\omega)$;
- whenever $\theta(\omega) \in S(\omega)$, the parameters lie in $[0, 1]$ and the PPV denominator
  $\pi\, \mathrm{se} + (1 - \pi)(1 - \mathrm{sp})$ is positive.

Then

$$
\mu\{\omega : \theta(\omega) \in S(\omega)\} \le
\mu\{\omega : \mathrm{PPV}(\theta(\omega)) \in T(\omega)\}:
$$

the coverage of the joint set transfers conservatively to the PPV output set, for any joint set,
rectangular or not. The inequality follows from the inclusion of the first event in the second; the
domain conditions make $\mathrm{PPV}(\theta(\omega))$ a genuine predictive value. No condition on
the denominator of the negative predictive value is imposed.
