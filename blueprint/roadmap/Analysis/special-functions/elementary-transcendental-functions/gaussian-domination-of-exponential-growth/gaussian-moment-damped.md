# Damping the datum shifts the Gaussian parameter

Let $G_n(f; p_1, p_2) = \int_{\mathbb{R}} y^n e^{-p_1 y^2 + p_2 y} f(y)\,dy$. For all $f : \mathbb{R} \to \mathbb{R}$, $n \in \mathbb{N}$ and real $a, p_1, p_2$: $G_n(f; p_1, p_2) = G_n\big(y \mapsto e^{-a y^2} f(y);\ p_1 - a,\ p_2\big)$.

Integrals here are Bochner integrals, under the convention that the integral of a non-integrable function is $0$; the statement holds for every function under that convention, and has its classical meaning when the integrands are integrable.
