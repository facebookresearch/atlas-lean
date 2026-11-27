# Stable finite-time blowup for arbitrarily large odd defocusing powers

Use $\mathbb T^{12}=(\mathbb R/2\pi\mathbb Z)^{12}$ and frequencies $n\in\mathbb Z^{12}$. For integer $k>8$, the $H^k$ datum is represented by $f\in\ell^2(\mathbb Z^{12};\mathbb C)$, with Fourier coefficient $(1+|n|^2)^{-k/2} f_n$. In physical variables the equation is $i\partial_t u+\Delta u=|u|^{p-1}u$. The free group $S(t)$ has multiplier $e^{-it|n|^2}$, and an interaction solution $v=S(-t)u$ starts at $f$ and solves $v'(t)=-i S(-t)(|S(t)v|^{p-1}S(t)v)$ in the weighted $H^k$ coordinates. The odd power is successive convolution/multiplication of $u$ with $u\bar u$, with conjugation corresponding to $f_n\mapsto\overline{f_{-n}}$. The source totalizes the weighted convolution to zero if it fails to be square summable; agreement with the product for $k>6$ is a prerequisite.

The maximal interaction domain $D_f$ is the union of all open intervals $(a,b)$ with $a<0<b$ carrying such a differentiable solution with the given datum. At $t\in D_f$ the maximal solution is obtained by choosing one patch containing $t$ and applying $S(t)$; outside $D_f$ the source assigns zero. A classical flow means $u(0)=f$, continuity into $H^k$ on $D_f$, and continuous differentiability into $H^{k-2}$ there with the equation holding in $H^{k-2}$. Changing from $H^k$ coordinates to $H^{k-2}$ multiplies by $(1+|n|^2)^{-1}$ and the free generator in the lower coordinates multiplies by $-i|n|^2/(1+|n|^2)$.


For every integer lower bound $p_0\ge0$ there exist integers $p\ge p_0$ odd with $p\ge3$, $k>8$, and a **nonempty open** subset $U$ of the above $H^k$ space. For every $f\in U$ the above flow is classical and there are $T>0$, $x\in\mathbb T^{12}$ and $c>0$ with $[0,T)\subseteq D_f$, $D_f$ bounded above with $\sup D_f=T$, and

$$ \lim_{t\uparrow T}(T-t)^{1/(p-1)} |u(t,x)|=c. $$

The time curve is not continuous into $H^k$ at $T$ from $(-\infty,T)$. Point evaluation here uses the sum of the continuous Fourier series with the weighted coefficients above. The assertion selects arbitrarily large odd powers; it does not claim this for every sufficiently large odd power.

## Expansion

Verify the weighted convolution estimates and that patch choice gives a unique flow on overlaps. Prove classical regularity in the lower Sobolev coordinates. Separate the construction and stability of a self-similar profile from the argument that the maximal right endpoint is finite and that the pointwise amplitude converges with the exact exponent.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DefocusingNLS.lean#L76-L275) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/371.md).
- OpenAI, [Stable self-similar blowup for a supercritical defocusing Schrödinger equation on the torus](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/paper.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
