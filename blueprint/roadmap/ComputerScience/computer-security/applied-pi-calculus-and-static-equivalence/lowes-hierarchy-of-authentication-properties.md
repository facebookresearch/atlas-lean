# Lowe's hierarchy of authentication properties

Whenever an honest agent $A$ completes a run of a protocol, apparently with another honest agent $B$, a protocol guarantees to $A$:

- *aliveness* if $B$ has previously run the protocol;
- *weak agreement* if $B$ has previously been running the protocol, apparently with $A$;
- *non-injective agreement* on a set of data $d$ if $B$ has previously been running the protocol, apparently with $A$, with the same data $d$;
- *injective agreement* on $d$ if moreover each such run of $A$ corresponds to a unique run of $B$, which excludes replays.

Each property implies the previous one. In the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md) with honest agents' public keys as parameters, each is a
[correspondence property](events-and-correspondence-properties.md) $e_{\mathrm{accept}}(t) \rightsquigarrow e_{\mathrm{begin}}(t)$ between an acceptance event of $A$ and a start event of $B$, with $t$ the
partner's identity, both identities, or both identities and $d$; injective agreement uses $\rightsquigarrow_{\mathrm{inj}}$.

## Depends on

- [Events and correspondence properties](events-and-correspondence-properties.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 6.3.2, Definitions 6.5–6.8 and their encodings as correspondence properties.
