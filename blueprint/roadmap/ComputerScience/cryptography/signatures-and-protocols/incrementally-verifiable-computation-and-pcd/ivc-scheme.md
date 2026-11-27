# Incrementally verifiable computation scheme for an iterated function

Let $F:\{0,1\}^{a}\times\{0,1\}^{b}\to\{0,1\}^{a}$ be a polynomial-time step function (state $z$, non-deterministic advice $w$). An *incrementally verifiable computation (IVC) scheme* for $F$ is a triple of polynomial-time algorithms $(\mathsf{G},\mathsf{P},\mathsf{V})$: $\mathsf{G}(1^\lambda)$ outputs public parameters $pp$; $\mathsf{P}(pp,i,z_0,z_i,w_i,\pi_i)$ outputs a proof $\pi_{i+1}$ for $z_{i+1}=F(z_i,w_i)$; and $\mathsf{V}(pp,i,z_0,z_i,\pi_i)\in\{0,1\}$.

*Completeness:* if $\mathsf{V}(pp,i,z_0,z_i,\pi_i)=1$ (with $\pi_0=\bot$ accepted for $i=0$) then $\pi_{i+1}=\mathsf{P}(pp,i,z_0,z_i,w_i,\pi_i)$ satisfies $\mathsf{V}(pp,i+1,z_0,F(z_i,w_i),\pi_{i+1})=1$.

*Knowledge soundness:* for every constant $n\in\mathbb{N}$ and every expected polynomial-time adversary $\mathsf{P}^*$ outputting $(z_0,z,\pi)$, there is an expected polynomial-time extractor $\mathsf{E}$, given the same input and randomness, outputting $w_0,\dots,w_{n-1}$ such that the probability that $\mathsf{V}(pp,n,z_0,z,\pi)=1$ but $z_n\ne z$, where $z_{i+1}=F(z_i,w_i)$, is negligible. The number of steps is a fixed parameter of the extractor because recursive extractors may blow up polynomially with each step; a scheme whose extractor also succeeds for $n=\mathrm{poly}(\lambda)$ satisfies a stronger property.

*Succinctness:* $|\pi_i|$ and the running time of $\mathsf{V}$ are bounded by $\mathrm{poly}(\lambda,|F|)$, independent of $i$.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Sources

- Paul Valiant, "Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency", TCC (2008).
- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370, Definition 5.
