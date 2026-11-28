# Probabilistic truncation of a secret-shared fixed-point value

Catrina and Saxena's protocol $\mathrm{TruncPr}$ maps a Shamir sharing of a signed $k$-bit integer $\bar a$ over $\mathbb{Z}_q$ to a sharing of $\lfloor\bar a/2^m\rfloor+u$, where the bit $u$ is $1$ with probability $(\bar a\bmod2^m)/2^m$, by opening $\bar a$ masked by a random integer whose summands each carry $\kappa$ extra bits.

Setting: $n$ parties, Shamir sharing of degree $t$ over a prime field $\mathbb{Z}_q$ (any $t+1$ shares reconstruct; a passive adversary corrupts at most $t$), $q>n$ and $n>2t$; statistical parameter $\kappa$, $\nu=\lceil\log_2\binom nt\rceil$, $q>2^{k+\kappa+\nu+1}$, and $0<m<k$. The input is a sharing $[a]$ of $a=\mathrm{fld}(\bar a)=\bar a\bmod q$ with $\bar a\in\mathbb{Z}_{\langle k\rangle}$.

1. $[b]\leftarrow2^{k-1}+[a]$, so $b=2^{k-1}+\bar a\in[0,2^k)$ and $b\bmod2^m=\bar a\bmod2^m$;
2. generate shared bits $r_0,\dots,r_{m-1}$ and set $[r']=\sum_{i<m}2^i[r_i]$; generate $[r'']$ with $r''$ the sum of $\binom nt$ integers in $[0,2^{\kappa+k-m})$; the bits, the summands and $\bar a$ are mutually independent and the bits and summands uniform; set $[r]=2^m[r'']+[r']$;
3. open $c=b+r$ (no reduction modulo $q$ occurs) and set $c'=c\bmod2^m$;
4. $[a']\leftarrow c'-[r']$ and $[d]\leftarrow([a]-[a'])\cdot(2^{-m}\bmod q)$.

Then $a'=(\bar a\bmod2^m)-u2^m$ with $u=\mathbf 1\{(\bar a\bmod2^m)+r'\ge2^m\}$, so $d=\mathrm{fld}(\lfloor\bar a/2^m\rfloor+u)$, and $\Pr[u=1]=(\bar a\bmod2^m)/2^m$, so the rounding is unbiased.

## Depends on

- [Fixed-point numbers encoded in a modular ring](fixed-point-ring-encoding.md)
- [Shamir threshold secret sharing](../../signatures-and-protocols/secure-multiparty-computation/secret-sharing-schemes/shamir-secret-sharing.md)

## Proof depends on

- [Linearity, multiplicativity and privacy of Shamir sharing](../../signatures-and-protocols/secure-multiparty-computation/secret-sharing-schemes/shamir-sharing-properties.md)

## Expansion

Correctness and the rounding law are the computation in step 4 and the uniformity of $r'$. Not ready: the generation of shared uniform bits ($\mathrm{PRandBitL}$) and of the shared sum-of-uniforms integer by pseudo-random replicated sharing ($\mathrm{PRandInt}$) have no pages. The source's statistical privacy claim relies on those building blocks and on a masking lemma for this joint mask distribution, conditioned on a coalition's view; independence of the bits and summands is essential (marginally uniform but correlated masks can fail to hide).

## Sources

- Octavian Catrina, Amitabh Saxena, "Secure Computation with Fixed-Point Numbers", Financial Cryptography and Data Security 2010, LNCS 6052, DOI 10.1007/978-3-642-14577-3_6, §§2.1–2.3, §3.1 (Protocol 3.1) and Tables 2–3.
