# Steps from a load

From `load dst src` with store $s$ and heap $h$, the only step is to `skip` with store $s[\mathit{dst} := h(s(\mathit{src}))]$ and the heap unchanged.
