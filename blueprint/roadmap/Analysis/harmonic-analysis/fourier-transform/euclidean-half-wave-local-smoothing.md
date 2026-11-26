# Euclidean half-wave local smoothing

On $\mathbb R^n$ use $\widehat f(\xi)=\int e^{-i x\cdot\xi}f(x)\,dx$ and inverse Fourier transform with phase $+ix\cdot\xi$ and factor $(2\pi)^{-n}$. Put $U_tf=\mathcal F^{-1}(e^{-it|\xi|}\widehat f)$ and $J^sf=\mathcal F^{-1}((1+|\xi|^2)^{s/2}\widehat f)$. For each integer $n\geq2$, real $p\geq2$ and loss $\varepsilon>0$ (or $p=2,\varepsilon=0$), put $s=\max(0,(n-1)/2-n/p)+\varepsilon$. There is a positive constant $C$ independent of the complex Schwartz function $f$ such that both $J^sf\in L^p(\mathbb R^n)$ and $U_tf\in L^p(\mathbb R^n\times[1,2],dx\,dt)$, and the latter norm is at most $C\|J^sf\|_p$. Here $p$ is finite.

## Depends on

The angular-frequency Fourier convention, Euclidean norm, actual inverse multiplier integrals, and the product of spatial volume with time volume restricted to the closed interval.

## Proof depends on

Frequency-localized local smoothing for the conic phase, summation over frequency bands with the positive loss, and the zero-loss $L^2$ estimate by Plancherel.

## Expansion

Separate the low frequency estimate, annular half-wave estimate with its frequency power, and Littlewood–Paley summation. State the membership and norms on the actual product measure; isolate the $p=2$ endpoint before using any positive loss.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L83-L97) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
