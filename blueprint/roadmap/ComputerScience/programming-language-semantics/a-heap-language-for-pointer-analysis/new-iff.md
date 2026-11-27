# Steps from an allocation

From `new dst a` with store $s$ and heap $h$, the only step is to `skip` with store $s[\mathit{dst} := a]$ and heap $h[a := 0]$, everything else unchanged. Allocation is not fresh: the allocation site $a$ is reused, and its heap cell reset to $0$, even if it was allocated before.
