# Signature of a path

The signature of a path $X : [s, t] \to \mathbb{R}^d$ is the family of its iterated integrals
$S(X)^{i_1 \cdots i_k}_{s,t} = \int_{s < t_1 < \cdots < t_k < t} dX^{i_1}_{t_1} \cdots dX^{i_k}_{t_k}$, one for every word
$i_1 \cdots i_k$, read as the coefficients of a tensor series. It is the non-commutative exponential of
the path: $t \mapsto S(X)_{s,t}$ solves the linear controlled equation $dS = S \otimes dX$, $S_{s,s} = 1$, so the
response of every linear controlled differential equation driven by $X$ is a linear function of
the signature (T. Lyons, *Rough paths, signatures and the modelling of functions on streams*,
Proc. ICM 2014, Definition 4.5 and Lemma 4.6). Chen's identity makes the signature a homomorphism
from concatenation of paths to the tensor product, which gives the signature of a piecewise-linear
path as a product of exponentials of its increments; Ree's shuffle identity makes the coordinate
iterated integrals an algebra of functions on paths, the starting point of the signature method in
machine learning (I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine
learning*, arXiv:1603.03788v2, §1.2–1.4).

Here paths are absolutely continuous and described by their velocity; Chen's identity and the
piecewise-linear formula need only a locally integrable velocity, the shuffle identity is stated
for a continuous velocity.

- [Signature of a path (iterated integrals)](signature.md)
- [Zeroth term of the signature](signature-nil.md)
- [Recursive definition of the signature](signature-concat.md)
- [First level of the signature is the increment](signature-singleton.md)
- [Signature of a path over a trivial interval](signature-self.md)
- [Continuity of the iterated integrals in the upper endpoint](continuous-signature.md)
- [Integrability of the integrand of the signature recursion](interval-integrable-signature-mul.md)
- [The signature solves $dS = S \otimes dX$](has-deriv-at-signature-concat.md)
- [Lower-endpoint derivative of an iterated integral (its value)](lower-deriv.md)
- [Derivative of the signature in its lower endpoint](has-deriv-at-signature-lower.md)
- [First-letter recursion of the signature](signature-cons.md)
- [Product of tensor series, coefficientwise](tensor-mul.md)
- [Unit tensor series](tensor-one.md)
- [Exponential of a vector in the tensor series algebra](tensor-exp.md)
- [Exponential of a scaled vector, coefficientwise](tensor-exp-smul.md)
- [Chen's identity](signature-chen.md)
- [Chen's identity, algebraic form](signature-eq-tensor-mul.md)
- [Signature of a linear segment is the exponential of its increment](signature-of-eq-on-ioc.md)
- [Signature of a piecewise-linear path](signature-piecewise-linear.md)
- [Signature along a repeated letter](signature-replicate.md)
- [Reparametrisation invariance of the signature](signature-comp.md)
- [Signature of the time-reversed path over a sub-interval](signature-reverse-eq.md)
- [Reversing the orientation of the interval](signature-swap.md)
- [Time-reversed signature, coordinate form](signature-reverse.md)
- [Time-reversed signature is the inverse](tensor-mul-signature-reverse.md)
- [Shuffle product of two words](shuffle.md)
- [Last-letter recursion of the shuffle product](shuffle-concat-concat.md)
- [Shuffle product identity (Ree)](signature-mul-signature.md)
- [Lévy area](levy-area.md)
- [Second level of the signature: increments and Lévy area](signature-pair-eq.md)
- [Composite linear map along a word](word-op.md)
- [Truncated signature series of a linear controlled equation](signature-series.md)
- [Picard recursion of the signature series](signature-series-succ.md)
- [Linear controlled equations are solved by the signature series](tendsto-signature-series.md)
- [Universal approximation by linear functionals of the signature](exists-signature-linear-approx.md)

## Related topics

- [Tree-like paths and uniqueness of the signature](../tree-like-paths-and-uniqueness-of-the-signature/README.md):
  which paths the signature cannot tell apart.
- [Rough paths and the extension theorem](../rough-paths-and-the-extension-theorem/README.md):
  the signature as the extension of a multiplicative functional, and its factorial decay.
- [Picard iteration](../../ordinary-differential-equations/picard-iteration/README.md):
  the Picard iterates of a linear controlled equation are the truncated signature series.
- [Euler method](../../numerical-analysis/euler-method/README.md): on each step the
  Euler scheme for a controlled equation uses only the first level of the signature, the
  increment; higher-order schemes for controlled equations use the higher levels.
- [Quadratic variation of Brownian motion](../../../Probability/stochastic-calculus/quadratic-variation-of-brownian-motion/README.md):
  Brownian paths have unbounded variation, so their iterated integrals are not Riemann–Stieltjes
  integrals; a rough path supplies the second level (the Lévy area) as extra data.
- [Itô integral](../../../Probability/stochastic-calculus/it-integral/README.md): the Itô (or
  Stratonovich) integral defines the iterated integrals of Brownian motion; the Stratonovich lift
  is the geometric rough path.
