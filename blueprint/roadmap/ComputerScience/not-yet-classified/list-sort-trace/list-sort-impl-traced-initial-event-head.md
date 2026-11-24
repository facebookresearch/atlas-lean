# List Sort Impl Traced initial event head

Every source-admitted raw top-level execution begins with exactly the
snapshot of the state returned by `initialMergeState`.  The theorem is stated
as a head equality so later lifecycle proofs need not unfold any scan branch.
