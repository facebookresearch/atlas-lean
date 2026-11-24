# Pattern Coding

Deterministic pattern coding. For any law `p` on finite response
patterns, the locally independent mixture whose latent state is the
pattern itself, and whose component at latent pattern `s` uses the
zero/one coordinates of `s` as success probabilities, reproduces `p`
exactly. The mixture is formed with `PMF.bind`; no support, positivity,
or independence assumption on `p` is imposed.
