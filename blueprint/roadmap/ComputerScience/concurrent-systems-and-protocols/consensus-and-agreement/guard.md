# Guard

Local instruction and channel guards. A reception consumes a previously sent, not already
received message. `H` is sampled only at an actual NACK. Delivery by the RB service is a separate
input whose causal integrity is imposed by `LegalPrefix` or by the article's broadcast primitive.
`wait p` has no instruction-readiness test; the separate actor guard requires `p` to be alive.
