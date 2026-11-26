# Polynomial Commitment Requested Trace

Honest transcript for one request batch selected *after* seeing the commitment. Given the
public key, draw a uniform bounded polynomial and commit to it. The request rule receives the
commitment, not the polynomial or decommitment; it chooses the whole ordered batch before any
answers are returned. Record the sampled polynomial, the requested batch (including its unserved
tail), and the view containing the commitment and honest replies. This is not an adaptive oracle.
