# Steps from a sequence

From `first; second` with store $s$ and heap $h$, a step either discards a leading `skip` (when `first` is `skip`), going to `second` with $s$ and $h$ unchanged, or takes a step of `first` from $(s, h)$ to some `first'` with store $s'$ and heap $h'$ and goes to `first'; second` with that updated store $s'$ and heap $h'$.
