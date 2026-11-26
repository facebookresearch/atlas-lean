# Maximum incoming bit load in a round

The load of a barrier is the maximum over recipients of the sum of incoming worker
and input-server message lengths at that recipient. In particular, neither a sender's total
nor the largest single message measures this load.
