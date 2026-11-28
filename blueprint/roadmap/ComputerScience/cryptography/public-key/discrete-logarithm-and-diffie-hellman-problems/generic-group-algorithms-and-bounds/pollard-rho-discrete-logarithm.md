# Pollard rho for discrete logarithms

Pollard's rho method with distinguished points finds discrete logarithms in a cyclic group of odd prime order $r$ by many short pseudorandom walks; under Galbraith's heuristic, the expected number of group elements an attempt samples, fresh starting points and walk steps together, is $(\sqrt{\pi/2}+o(1))\sqrt r$, and an attempt fails with probability $1/r$.

Let $g$ be an element of odd prime order $r$ of a group $G$ and $h\in\langle g\rangle$. Fix a selection function $S:\langle g\rangle\to\{0,\dots,n_S-1\}$ and precompute $g_j=g^{u_j}h^{v_j}$ with $u_j,v_j$ uniform in $\{0,\dots,r-1\}$. The *original rho walk* is $x_{i+1}=x_i^2$ if $S(x_i)=0$ and $x_{i+1}=x_ig_j$ if $S(x_i)=j\ne0$; the *additive walk* is $x_{i+1}=x_ig_{S(x_i)}$. Each walk step costs one group operation and keeps a representation $x_i=g^{a_i}h^{b_i}$. A set of *distinguished points* is fixed by a property of the binary representation of group elements, holding for a proportion $\theta$ of $\langle g\rangle$.

**One attempt.** Start walks one after another at $g^{a_0}h^{b_0}$ with $(a_0,b_0)$ uniform and independent for each walk; run each walk until it reaches a distinguished point and store that point with its representation. Stop at the first distinguished point reached by two different walks, $g^{a}h^{b}=g^{a'}h^{b'}$. If $b\not\equiv b'\pmod r$ output

$$
\log_g h\equiv (a'-a)(b-b')^{-1}\pmod r ;
$$

otherwise the attempt fails.

**Theorem (Galbraith, Theorem 14.2.16, with the sampled-element count of its heuristic).** Assume Heuristic 14.2.15: walks reach a distinguished point in significantly fewer than $\sqrt r$ steps, without cycles, and the group elements visited by the attempt behave like independent uniform samples, so that the expected number of group elements sampled before the first collision is $\sqrt{\pi r/2}$; assume also $\theta>\log(r)/\sqrt r$. Count one step for each group element the attempt visits, whether a fresh starting point or the output of a walk step. Then the expected number of steps of one attempt is $(\sqrt{\pi/2}+o(1))\sqrt r$, and the attempt fails with probability $1/r$.

## Depends on

- [Discrete-logarithm experiment](../../hardness-assumptions/dlog-game.md)

## Proof depends on

None.

## Expansion

Galbraith states the theorem in group operations and his proof counts steps as calls to the walk function; the count here is of sampled group elements, the quantity his heuristic controls, so fresh starting points are counted too. The proof: under the heuristic no visited element is wasted, so after $N$ steps $N$ group elements have been visited, and the first collision occurs after an expected $\sqrt{\pi r/2}$ steps; detection at the next distinguished point adds $2/\theta<2\sqrt r/\log r=o(\sqrt r)$ steps, using Lemma 14.2.14 for uniformly sampled elements. The failure probability uses that the two walks start from independent uniform representations and that each walk step maps the coefficient pair $(a,b)$ by an invertible affine map modulo $r$ (doubling for a squaring step, invertible because $r$ is odd; adding $(u_j,v_j)$ otherwise), so $b$ and $b'$ are independent and uniform and $b\equiv b'$ with probability $1/r$. A failed attempt is repeated with fresh independent choices. The step count is not a count of group operations: computing a fresh starting point $g^{a_0}h^{b_0}$ takes $O(\log r)$ group operations by square-and-multiply, and the precomputation of $g_1,\dots,g_{n_S-1}$ takes $O(n_S\log r)$; these costs come on top of the step count. The heuristic models the walk by uniform sampling, for which the expected number of samples from a set of $N$ elements before a repeat is less than $\sqrt{\pi N/2}+2$ (Galbraith, Theorem 14.1.1); for a uniformly random function $V\to V$ the expected time to the first repeat is asymptotic to $\sqrt{\pi N/2}$ (Sutherland, Theorem 9.3).

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 14.2.1, Definition 14.2.11, Lemma 14.2.14, Theorem 14.1.1, Heuristic 14.2.15 with the assumptions stated before it, and Theorem 14.2.16 with its proof.
- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 9 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes9.pdf>, Theorem 9.3.
