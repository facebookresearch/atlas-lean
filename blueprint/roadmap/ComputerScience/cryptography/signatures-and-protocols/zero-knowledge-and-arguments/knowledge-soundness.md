# Knowledge soundness

Let $R$ be a binary relation with language $L_R = \{x : (x, w) \in R \text{ for some } w\}$, let $V$ be a verifier of an interactive protocol computable in probabilistic polynomial time, and let $\kappa : \{0,1\}^* \to [0,1]$. For a prover strategy $P$ and an input $x$, let $p(x)$ be the probability that $V$ accepts on common input $x$ after interacting with $P$. Then $V$ is a *knowledge verifier* for $R$ with *knowledge error* $\kappa$ if

- *non-triviality*: some prover strategy makes $V$ accept with probability $1$ on every $x \in L_R$, in particular with probability above $\kappa(x)$ whenever $\kappa(x) < 1$; and
- *validity*: there are a constant $c > 0$ and a probabilistic oracle machine $K$, the *knowledge extractor*, such that for every prover strategy $P$ and every $x \in L_R$ with $p(x) > \kappa(x)$, the machine $K$ on input $x$ with oracle access to $P$ on input $x$ outputs some $w$ with $(x, w) \in R$ within an expected number of steps at most $|x|^c / (p(x) - \kappa(x))$.

This is the definition of Bellare and Goldreich; it says nothing about inputs outside $L_R$, where soundness is a separate requirement, and the *strong* variant of validity, which quantifies over every input $x$, also bounds the acceptance probability by $\kappa(x)$ there, since no witness exists. In particular, when $\kappa$ is negligible and $P$ convinces $V$ with non-negligible probability, the extractor runs in expected polynomial time. For argument systems, *knowledge soundness* is used in the following asymptotic form: whenever a prover strategy that runs in polynomial time convinces the verifier with non-negligible probability, a polynomial-time extractor that may interact repeatedly with that prover outputs a witness with non-negligible probability; an argument system with this property is an *argument of knowledge*.

## Depends on

- [Interactive arguments](interactive-arguments.md)

## Sources

- M. Bellare and O. Goldreich, "On defining proofs of knowledge", *CRYPTO 1992*, LNCS 740, Springer, 1993, <https://cseweb.ucsd.edu/~mihir/papers/pok.pdf>, Definition 3.1 and Section 4.1
- J. Thaler, *Proofs, Arguments, and Zero-Knowledge*, Foundations and Trends in Privacy and Security 4(2–4), 2022, <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf>, Section 7.4
