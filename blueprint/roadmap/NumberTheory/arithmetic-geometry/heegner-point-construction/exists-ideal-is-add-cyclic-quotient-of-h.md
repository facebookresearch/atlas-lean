# An ideal of index `N` under the Heegner hypothesis

Let `K` be an imaginary quadratic field
with ring of integers `𝓞 K` and let `N ≥ 1` be an integer such that every prime factor `p` of `N`
splits in `K`: `p 𝓞 K = P Q` with `P ≠ Q` prime ideals. Then there is an ideal `𝒩` of `𝓞 K` such
that the additive group `𝓞 K ⧸ 𝒩` is cyclic of order `N`.

The proof takes `𝒩 = ∏_{p ∣ N} P_p ^ {v_p(N)}`; it does not use that `K` is imaginary
(`exists_ideal_quotient_ringEquiv_zmod_of_finrank_eq_two`).

## Sources

- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero and one*, LMS J. Comput. Math. 14 (2011), 327–350, §4, p. 335 ("By hypothesis, there is an ideal $\mathcal{N}$ of $\mathcal{O}_K$ such that $\mathcal{O}_K/\mathcal{N}$ is cyclic of order $N$"); B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256, §1, p. 235 ("Choose an ideal $\mathcal{N}$ of $\mathcal{O}$ with $\mathcal{O}/\mathcal{N} \simeq \mathbb{Z}/N\mathbb{Z}$").
