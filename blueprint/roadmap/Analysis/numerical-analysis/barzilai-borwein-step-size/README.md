# Barzilai–Borwein step size

The two-point step-size gradient method of Barzilai and Borwein iterates $x_{k+1} = x_k - \alpha_k \nabla f(x_k)$ with $\alpha_k = s^\top s / s^\top y$ (or $s^\top y / y^\top y$), where $s$ and $y$ are the latest changes of the iterate and of the gradient: the scalar matrix $\alpha_k^{-1} I$ is a least-squares fit of the secant equation. The method is nonmonotone, converges globally on strictly convex quadratics (Raydan) and is often much faster than steepest descent with exact line searches.

- [First Barzilai–Borwein step size](bb-step.md)
- [Second Barzilai–Borwein step size](bb-step-2.md)
- [The first Barzilai–Borwein step is a least-squares secant fit](norm-inv-bb-step-smul-sub-le.md)
- [The second Barzilai–Borwein step is a least-squares secant fit](norm-sub-bb-step-smul-le.md)
- [The second Barzilai–Borwein step is the shorter one](bb-step-le-bb-step.md)
- [Barzilai–Borwein steps on a quadratic lie between the inverse curvature bounds](bb-step-mem-icc.md)
- [Raydan's theorem](raydan-tendsto-gradient.md)

## Related topics

- [Quasi-Newton methods](../quasi-newton-methods/README.md): the secant equation that the step fits.
- [Gradient descent](../../convex-analysis-and-variations/gradient-descent/README.md): gradient descent with constant or scheduled steps, which the two-point
  step size replaces.
