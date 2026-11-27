# Rough paths and the extension theorem

A rough path is a path together with enough of its iterated integrals to make its driven
differential equations well posed. Lyons captured this through multiplicative functionals:
maps $(s, t) \mapsto X_{s,t}$ into the truncated tensor algebra $T^{(n)}$ with $X^0 = 1$ and
$X_{r,s} \otimes X_{s,t} = X_{r,t}$, the algebraic content of Chen's identity, controlled in
$p$-variation by $\|X^i_{s,t}\| \le \omega(s,t)^{i/p} / (\beta\,(i/p)!)$. The signature of a path
of bounded variation is the basic example, with $p = 1$. For a $p$-rough path, $n = \lfloor p
\rfloor$ levels are the right amount of data: the extension theorem says they determine all higher
levels, in particular the signature, and the universal limit theorem says
that solutions of controlled differential equations depend continuously on these levels in
$p$-variation, which gives a pathwise meaning to Stratonovich equations driven by Brownian motion
lifted with its Lévy area, $2 < p < 3$ (T. Lyons, *Differential equations driven by rough
signals*, Rev. Mat. Iberoam. 14 (1998), §2.1–2.2).

- [Multiplicative functional of degree $n$ (Lyons)](is-multiplicative-functional.md)
- [Control function (Lyons)](is-control.md)
- [Norm of a tensor level](level-norm.md)
- [$p$-variation controlled by $\omega$ (Lyons)](is-controlled-by.md)
- [Finite $p$-variation of degree $n$](has-finite-pvariation.md)
- [The signature is a multiplicative functional](is-multiplicative-functional-signature.md)
- [The length of a path is a control](is-control-length.md)
- [Factorial decay of the signature](level-norm-signature-le.md)
- [The signature of a continuously differentiable path is controlled by its length, with $p = 1$](is-controlled-by-signature.md)
- [Signatures of continuously differentiable paths have finite $1$-variation in every degree](has-finite-pvariation-signature.md)
- [Lyons's extension theorem: existence and uniqueness](exists-unique-extension.md)
- [Lyons's extension theorem: the factorial estimate](is-controlled-by-extension.md)

## Related topics

- [Signature of a path](../signature-of-a-path/README.md): the iterated integrals of a path of
  bounded variation, the model case $p = 1$; Chen's identity is the multiplicative property.
- [Quadratic variation of Brownian motion](../../../Probability/stochastic-calculus/quadratic-variation-of-brownian-motion/README.md):
  Brownian paths have finite $p$-variation only for $p > 2$, so they need two levels.
