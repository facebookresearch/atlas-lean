# The real PRG world is the CPA experiment

For every chosen-plaintext adversary, the CPA indistinguishability experiment against the stream
cipher is the real world of the PRG experiment for the distinguisher built from the adversary: with
keystream $G(k)$, the distinguisher runs the CPA experiment exactly.
