# Shannon's channel coding theorem

For a discrete memoryless channel with capacity $C$ (in bits), every rate below $C$ is achievable
with vanishing maximal error probability, and no rate above $C$ is. Achievability follows from
Gallager's random coding bound and a maximum-likelihood decoder; the weak and strong converses bound
the rates from above.

## Achievability

- [Shannon's channel coding theorem, achievability](channel-coding-achievability.md)
- [A maximum-likelihood decoder exists](exists-ml-decoder.md)
- [Maximum-likelihood decoding errs only on ties or worse](measure-real-pi-le-ml-error-prob.md)

## Converses

- [Strong converse for discrete memoryless channels](channel-coding-strong-converse.md)
- [Weak converse for discrete memoryless channels](channel-coding-weak-converse.md)

## Related topics

- [Fano's inequality](../../information-inequalities/fano-s-inequality/README.md)
- [Random coding bound and Gallager's exponent](../random-coding-bound-and-gallager-s-exponent/README.md):
  the random coding bound and its expurgated form, from which achievability follows.
- [Shannon's source coding theorem](../../source-coding/shannon-s-source-coding-theorem/README.md)
- [Bounds on code size](../../error-correcting-codes/bounds-on-code-size/README.md)
- [List decoding](../../error-correcting-codes/list-decoding/README.md): for worst-case errors, list decoding with small lists reaches the rate $1 - H_q(\rho)$, the capacity of the $q$-ary symmetric channel.
