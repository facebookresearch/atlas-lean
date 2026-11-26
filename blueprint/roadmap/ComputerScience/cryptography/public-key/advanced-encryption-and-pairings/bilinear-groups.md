# Bilinear groups

Let $\mathbb{G}$, $\hat{\mathbb{G}}$ and $\mathbb{G}_T$ be cyclic groups of the same prime order $p$, written multiplicatively. A *bilinear pairing* is a map $e : \mathbb{G} \times \hat{\mathbb{G}} \to \mathbb{G}_T$ with two algebraic properties:

- *Bilinearity*: $e(g^a, h^b) = e(g, h)^{ab}$ for all $g \in \mathbb{G}$, $h \in \hat{\mathbb{G}}$ and $a,b \in \mathbb{Z}_p$.
- *Non-degeneracy*: $e(g,h) \ne 1$ for at least one pair. In particular, if $g$ and $h$ generate their respective groups, then $e(g,h)$ generates $\mathbb{G}_T$. Otherwise $e(g,h)$ would be the identity (the target has prime order), and bilinearity would send every pair of powers of $g,h$ to the identity.

When the source groups coincide, write $x=g^a$ and $y=g^b$ for a common generator $g$. Then $e(x,y)=e(g,g)^{ab}=e(y,x)$, and $e(g,g)$ generates $\mathbb{G}_T$ for every generator $g$. More generally, Kate, Zaverucha and Goldberg call a pairing *symmetric* (type 1) when there is an efficiently computable isomorphism $\varphi:\hat{\mathbb{G}}\to\mathbb{G}$ whose inverse is also efficiently computable. In that case the symmetry identity is $e(x,\hat y)=e(\varphi(\hat y),\varphi^{-1}(x))$. The identity isomorphism recovers the equal-source case; without an identification, simply swapping arguments from different groups is not defined.

A pairing is *admissible* if, in addition to the algebraic conditions, it is efficiently computable. After identifying the two source groups as above, an admissible pairing gives a *symmetric bilinear group*. For a family with given bitstring representations, efficient computation means that **one** algorithm, given the encoded public group parameter and the two encoded elements, returns the encoded pairing value in time polynomial in the input length. Both the algorithm and its polynomial bound are independent of the parameter. A separate lookup table for each finite group does not establish uniform polynomial-time evaluation.

## Sources

- D. Boneh and M. Franklin, [“Identity-Based Encryption from the Weil Pairing”](https://crypto.stanford.edu/~dabo/papers/bfibe.pdf), *SIAM Journal on Computing* 32(3):586–615, 2003, opening of Section 3, immediately before Section 3.1 (admissible bilinear maps, written additively in the first group).
- A. Kate, G. M. Zaverucha and I. Goldberg, [*Polynomial Commitments*](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), technical report CACR 2010-10, Appendix A, pp. 18–19 (the extended version of “Constant-Size Commitments to Polynomials and Their Applications”).
