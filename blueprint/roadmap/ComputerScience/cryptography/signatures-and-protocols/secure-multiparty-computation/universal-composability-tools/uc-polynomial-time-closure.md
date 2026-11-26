# Polynomial-time closure of UC executions

Call a family of interactive machines strict polynomial time (PPT) if each activation runs in time polynomial in the security parameter and the length of its input, with replies of polynomially bounded length. Then: (i) linking a PPT environment with a reply-bounded PPT machine family yields a PPT environment, provided the total input length the environment receives stays polynomially bounded; (ii) absorbing a reply-bounded PPT adversary (or hybrid protocol) into a PPT environment preserves the PPT property, which is what makes the dummy-adversary reduction stay within the class of efficient environments; (iii) the UC execution of a PPT protocol, adversary and environment is PPT in the security parameter; (iv) static-corruption routing and the lifting wrappers that adapt interfaces preserve reply-boundedness and PPT certificates.

## Proof sketch

Compose the running-time bounds activation by activation: the number of activations is bounded by the environment's running time, and each activation's input is bounded by the reply bounds of the machines that produced it.

## Depends on

- [Interactive machines, linking and the single-token execution model](uc-interactive-machines.md)
- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Sources

- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
