# The alternating-bit protocol with data in a configuration

For a configuration $c$ made of
a sender state $s$, a data-channel content $d$, a receiver state $r$ and an
acknowledgement-channel content $k$, the protocol process at $c$ is
$((X_s \mid X_d) \mid X_r) \mid X_k$ with every internal channel restricted, where $X_s$, $X_d$,
$X_r$ and $X_k$ are the process constants of these states. The internal channels are all channel
names other than accepting and delivering a data bit.
