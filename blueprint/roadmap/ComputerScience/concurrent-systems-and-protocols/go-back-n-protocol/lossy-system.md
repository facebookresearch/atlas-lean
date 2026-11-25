# The lossy go-back-N process in a configuration

Let $c$ be a configuration of the lossy
variant, and let $S$, $D$, $R$ and $A$ be the process constants for its sender state, its
data-channel content, its receiver state (as a receiver of the lossy variant) and its
acknowledgement-channel content. The process of the lossy variant in $c$ is
$((S \mid D) \mid R) \mid A$ with the internal channels of the lossy variant restricted.
