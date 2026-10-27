---
article_id: af_abb09f9640618b38dd75fc1a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierAnalysis.fourier_schwartz_equiv
---

# Definition 17.4

The Fourier transform of a Schwartz function $f \in \mathcal{S}(\mathbb{R})$ is the function $$\hat{f}(y)\coloneqq \int_{\mathbb{R}} f(x) e^{-2 \pi i x y} d x$$ which is also a Schwartz function. We can recover $f(x)$ from $\hat{f}(y)$ via the inverse transform $$f(x)=\int_{\mathbb{R}} \hat{f}(y) e^{+2 \pi i x y} d y.$$ The maps $f \mapsto \hat{f}$ and $\hat{f} \mapsto f$ are thus inverse linear operators on $\mathcal{S}(\mathbb{R})$ (they are also continuous in the metric topology of $\mathcal{S}(\mathbb{R})$ and thus homeomorphisms).

## Depends on

- [Definition 17.1](339-definition-17-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 17.1](../../../../../sources/v1/NumberTheoryI.md)
