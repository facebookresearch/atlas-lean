---
article_id: af_46674270173975346d100413
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierAnalysis.fourier_gaussian_complex
---

# Proposition 3.0.3 (The Fourier transform of a Gaussian is another Gaussian)

Let $f(x)= \exp(-\pi z|x|^{2})$, where $z=a+ib$ is a complex number, $a, b \in \mathbb{R}$, $a>0$, $x=(x^{1}, \cdots, x^{n}) \in \mathbb{R}^{n}$, and $|x|^{2}=\sum_{j=1}^{n}(x^{j})^{2}$. Then $\hat{f}(\xi)=z^{-n/2} \exp(-\pi|\xi|^{2}/z)$.

## Depends on

- [Definition 1.0.1 (Fourier Transform)](069-fourier-transform.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #16, Section 3](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
