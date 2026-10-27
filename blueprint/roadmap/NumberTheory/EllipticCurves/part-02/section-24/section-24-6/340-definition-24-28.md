---
article_id: af_810093410f0b4f4dd2f4dc8d
declaration: def
origin: cited
lean: EllipticCurveLFunction.LFunction
---

# Definition 24.28

The $L$-function of an elliptic curve $E/\mathbb{Q}$ is given by the Euler
 product $L(E, s)=\prod_{p} L_{p}(p^{-s})^{-1}=\prod_{p}(1-a_{p}
 p^{-s}+\chi(p) p p^{-2s})^{-1}$, where $\chi(p)$ is 0 if $E$ has bad
 reduction at $p$, and 1 otherwise. For primes $p$ where $E$ has good
 reduction, $a_{p}\coloneqqp+1-\# E_{p}(\mathbb{F}_{p})$ is the trace of
 Frobenius, where $E_{p}$ denotes the reduction of $E$ modulo $p$.
 Equivalently, $L_{p}(T)$ is the numerator of the zeta function $Z(E_{p};
 T)=\exp(\sum_{n=1}^{\infty} \# E_{p}(\mathbb{F}_{p^{n}})
 \frac{T^{n}}{n})=\frac{1-a_{p} T+p T^{2}}{(1-T)(1-p T)}$. For primes $p$
 where $E$ has bad reduction, $L_{p}(T)=1$ if $E$ has additive reduction at
 $p$, $L_{p(T)=1-T$ if $E$ has split multiplicative reduction at $p$, and
 $L_{p}(T)=1+T$ if $E$ has non-split multiplicative reduction at $p$. This
 means that $a_{p} \in \{0, \pm 1\}$ at bad primes. The $L$-function $L(E,
 s)$ converges to a holomorphic function on $\operatorname{re}(s)>3/2$.

## Depends on

- [Definition 3.2](../../../part-01/section-3/section-3-1/006-definition-3-2.md)
- [Definition 4.24](../../../part-01/section-4/section-4-3-3/047-definition-4-24.md)
- [Definition 6.17](../../../part-01/section-6/100-definition-6-17.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 24.6](../../../../../../sources/v1/EllipticCurves.md)
