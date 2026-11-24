# Top Level Formed Lengths

Paper-facing formed-run lengths for a real top-level execution.

Inputs of length zero and one bypass the scan, so their genuine policy-event
stream is empty.  The singleton leaf is introduced only at this semantic
normalization boundary; no synthetic `.formed` observation is added to the
machine trace.
