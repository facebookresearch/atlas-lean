# Vector clocks characterize happened-before

Let $e_0, \dots, e_{n-1}$ be an execution and $a, b < n$ positions of it. The event at $a$ happened before the event at $b$ if and only if the vector timestamp of $a$ is smaller than that of $b$ in the pointwise order: it is at most the timestamp of $b$ in every component and differs from it in some component.
