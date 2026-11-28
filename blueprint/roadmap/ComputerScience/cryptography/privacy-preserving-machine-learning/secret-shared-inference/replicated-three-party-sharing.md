# Replicated three-party secret sharing with zero-sharing multiplication

In *replicated 2-out-of-3 sharing* over $\mathbb{Z}_{2^k}$ a secret $x=x_1+x_2+x_3$ is held as pairs, party $i$ holding $(x_i,x_{i+1})$. To multiply, party $i$ computes $z_i=x_iy_i+x_{i+1}y_i+x_iy_{i+1}$ and sends $z_i+\alpha_i$ to party $i-1$, where $\alpha_1+\alpha_2+\alpha_3=0$ is a fresh zero sharing and party $i$ holds $\alpha_i$.

Indices are modulo $3$. A sharing of $x$ consists of $x_1,x_2,x_3$ uniform subject to $x_1+x_2+x_3=x$, so any two parties together hold all three shares, and a single party's pair is uniform and independent of $x$. A linear combination $ax+by+c$ with public $a,b,c$ is computed locally, with $c$ added to the first share. For a product, $z_1,z_2,z_3$ form a 3-out-of-3 sharing of $xy$, because each of the nine terms $x_jy_{j'}$ occurs exactly once among them; after resharing, party $i$ holds $(z_i+\alpha_i,\,z_{i+1}+\alpha_{i+1})$, a 2-out-of-3 sharing of $xy$. With *ideal* correlated randomness, each zero sharing is uniform on $\{(\alpha_1,\alpha_2,\alpha_3):\sum\alpha_i=0\}$ and party $i$ receives $\alpha_i$. In the *PRF* realization (Falcon's convention), a one-time setup has each party $i$ draw a uniform key $k_i$ of a PRF $F$ with outputs in $\mathbb{Z}_{2^k}$ and send it to party $i+1$, so party $i$ holds $k_i$ and $k_{i-1}$; the zero sharing at counter value $j$ is $\alpha_i=F_{k_i}(j)-F_{k_{i-1}}(j)$, with $j$ incremented after each use. The three values sum to zero and are pseudorandom rather than uniform.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../../symmetric-key/pseudorandom-functions/prfsecure.md)

## Proof depends on

None.

## Expansion

A definition of the sharing and of the multiplication procedure; no security statement is made here. Evans, Kolesnikov and Rosulek describe the same PRF zero sharing with the key pairs indexed the other way, party $i$ holding $(k_i,k_{i+1})$ and computing $F_{k_i}(j)-F_{k_{i+1}}(j)$, for a PRF with outputs in a field.

## Sources

- Sameer Wagh, Shruti Tople, Fabrice Benhamouda, Eyal Kushilevitz, Prateek Mittal, Tal Rabin, "Falcon: Honest-Majority Maliciously Secure Framework for Private Deep Learning", Proceedings on Privacy Enhancing Technologies 2021(1), pp. 188–208, DOI 10.2478/popets-2021-0011, [journal copy](https://petsymposium.org/popets/2021/popets-2021-0011.pdf): §3.1 (notation and share pairs) and §3.2 ($\Pi_{\mathrm{Mult}}$ and resharing, correlated randomness, linear operations), p. 193; Figure 6 ($\Pi_{\mathrm{Prep}}$ setup), p. 207.
- David Evans, Vladimir Kolesnikov, Mike Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, NOW Publishers (2018), [authors' copy](https://securecomputation.org/docs/pragmaticmpc.pdf) (version of June 11, 2022): §7.1.2 ("Three-Party Secret Sharing"), pp. 128–130.
