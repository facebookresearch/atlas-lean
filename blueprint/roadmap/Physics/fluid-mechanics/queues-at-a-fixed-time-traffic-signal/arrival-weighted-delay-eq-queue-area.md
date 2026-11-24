# Occupancy identity for the cycle

For one clearing cycle, the virtual delay of each
vehicle arriving in `[0, R + G)`, integrated against the arrival measure
`ENNReal.ofReal lam • volume`, equals the queue area over `[0, R + G]`: the total waiting of the
vehicles that arrive in the cycle is the time integral of the queue length. The area itself is
the one-cycle area formula `queueLen_integral_cycle`.
