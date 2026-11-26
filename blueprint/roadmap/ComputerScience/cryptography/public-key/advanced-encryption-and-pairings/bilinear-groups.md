# Bilinear groups

Let $\mathbb{G}$, $\hat{\mathbb{G}}$ and $\mathbb{G}_T$ be cyclic groups of the same prime order $p$, written multiplicatively. A *bilinear pairing* is a map $e : \mathbb{G} \times \hat{\mathbb{G}} \to \mathbb{G}_T$ with two algebraic properties:

- *Bilinearity*: $e(g^a, h^b) = e(g, h)^{ab}$ for all $g \in \mathbb{G}$, $h \in \hat{\mathbb{G}}$ and $a,b \in \mathbb{Z}_p$.
- *Non-degeneracy*: $e(g,h) \ne 1$ for at least one pair. In particular, if $g$ and $h$ generate their respective groups, then $e(g,h)$ generates $\mathbb{G}_T$. Otherwise $e(g,h)$ would be the identity (the target has prime order), and bilinearity would send every pair of powers of $g,h$ to the identity.

In the *symmetric* case the two source groups coincide. Writing $x=g^a$ and $y=g^b$ for a common generator $g$ gives $e(x,y)=e(g,g)^{ab}=e(y,x)$. Moreover, $e(g,g)$ generates $\mathbb{G}_T$ for every generator $g$. In the asymmetric case the two source groups need not coincide, so swapping arguments need not even be defined.

A pairing is *admissible* if, in addition, it is efficiently computable. With equal source groups, $(\mathbb{G}, \mathbb{G}_T,e)$ is then a *symmetric bilinear group*. For a family with given bitstring representations, efficient computation means that **one** algorithm, given the encoded public group parameter and the two encoded elements, returns the encoded pairing value in time polynomial in the input length. Both the algorithm and its polynomial bound are independent of the parameter. A separate lookup table for each finite group does not establish uniform polynomial-time evaluation.

## Sources

- D. Boneh and M. Franklin, [“Identity-Based Encryption from the Weil Pairing”](https://crypto.stanford.edu/~dabo/papers/bfibe.pdf), *SIAM Journal on Computing* 32(3):586–615, 2003, opening of Section 3, immediately before Section 3.1 (admissible bilinear maps, written additively in the first group).
- A. Kate, G. M. Zaverucha and I. Goldberg, [*Polynomial Commitments*](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), technical report CACR 2010-10, Appendix A, pp. 18–19 (the extended version of “Constant-Size Commitments to Polynomials and Their Applications”).
