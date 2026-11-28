# Dual distinguishing attack on decision LWE

The dual attack computes from $A$ alone a short $v$ with $vA\equiv0\pmod q$ having some coordinate invertible modulo $q$, and tests whether $\langle v,c\rangle$ is small: for LWE samples it equals $\langle v,e\rangle$, for uniform $c$ it is uniform. Lindner–Peikert's model estimates the advantage as about $\exp(-\pi(\|v\|\alpha)^2)$.

Let $(A,c)\in\mathbb{Z}_q^{m\times n}\times\mathbb{Z}_q^m$ be either LWE samples $c=As+e$ with errors from the discrete Gaussian $D_{\mathbb{Z},\alpha q}$ of width parameter $\alpha q$ (density proportional to $\exp(-\pi x^2/(\alpha q)^2)$), or uniform. Let

$$
L_A=\{w\in\mathbb{Z}^m:\ wA\equiv 0 \pmod q\}.
$$

**Attack.** From $A$ and internal randomness only, without looking at $c$, compute by lattice reduction a short $v\in L_A$ that has at least one coordinate invertible modulo $q$ (a *usable* vector; nonzero vectors such as $q\varepsilon_i$ lie in $L_A$ but are useless). If no usable vector is found, report failure; for example, if $q$ is prime and $A$ is square and invertible modulo $q$, then $L_A=q\mathbb{Z}^m$ has no usable vector. Otherwise output a guess from the centred residue of $\langle v,c\rangle$ modulo $q$, for instance "LWE" if it is small.

- If $c=As+e$, then $\langle v,c\rangle\equiv\langle v,e\rangle \pmod q$ exactly, because $vA\equiv0$.
- If $c$ is uniform and independent of $A$, and $v$ is usable and computed from $A$ and randomness independent of $c$, then $\langle v,c\rangle$ is uniform on $\mathbb{Z}_q$.

**Advantage model.** Albrecht, Player and Scott, following Lindner and Peikert, state that the advantage of distinguishing $\langle v,e\rangle$ from uniform is close to $\exp\bigl(-\pi(\|v\|\,\alpha)^2\bigr)$; this is a heuristic advantage estimate, not a success probability. The BKZ model gives $\|v\|\approx\delta_0^{m}q^{n/m}$ when $L_A$ has volume $q^n$ (for instance $q$ prime, $m\ge n$, $A$ of rank $n$ modulo $q$); for fixed $\delta_0>1$, ignoring integrality and the available number of samples, this is minimised at $m=\sqrt{n\log q/\log\delta_0}$.

## Proof sketch

Exactness: $\langle v,As+e\rangle=(vA)s+\langle v,e\rangle$ and $vA\equiv0$. Uniformity: conditional on $A$ and the randomness that produced $v$, $c$ is still uniform, and for a usable $v$ the map $c\mapsto\langle v,c\rangle$ is a surjective homomorphism $\mathbb{Z}_q^m\to\mathbb{Z}_q$ with equal-size fibres. If $v$ were chosen after seeing $c$ (say orthogonal to $c$) the conclusion would fail. The advantage model treats $\langle v,e\rangle$ as a Gaussian of width about $\|v\|\alpha q$ reduced modulo $q$; Albrecht, Player and Scott use it to choose the target length for a desired advantage (their Corollary 2) and note that accepting longer vectors and repeating on fresh, independent samples can be cheaper; tests reusing the same samples are correlated and need separate analysis. Variants for small or sparse secrets (Albrecht 2017) and dual-hybrid attacks exist and are not covered here.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [The block Korkine–Zolotarev (BKZ) reduction algorithm](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/bkz-algorithm.md)
- [Root-Hermite factor and the geometric series assumption](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/root-hermite-factor-and-geometric-series-assumption.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)
- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)

## Proof depends on

None.

## Sources

- Martin R. Albrecht, Rachel Player, Sam Scott, "On the concrete hardness of Learning with Errors", Journal of Mathematical Cryptology 9(3):169–203, 2015; IACR ePrint 2015/046, [https://eprint.iacr.org/2015/046](https://eprint.iacr.org/2015/046), Section 4.1, Lemma 6, Remark 2 and Corollary 2.
- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", in Protecting Privacy through Homomorphic Encryption, Springer, 2021, pp. 31–62; IACR ePrint 2019/939, [https://eprint.iacr.org/2019/939](https://eprint.iacr.org/2019/939), Section 2.1.2 c.
