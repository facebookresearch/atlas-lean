# Nonce digests close to uniform

A keyed hash satisfies the hiding hypothesis with key $s$ and error $\varepsilon \ge 0$ when, for every
message, the nonce digest is within statistical distance $\varepsilon$ of the uniform distribution on
digests. The key is fixed and only the nonce is random, so this is an assumption on the fixed function
$H_s$; it is not a consequence of collision resistance or of hiding in the random-oracle model
(stated here without proof). For example, with a single nonce and two digests, every nonce digest is
a point mass, at distance $\tfrac{1}{2}$ from uniform.
