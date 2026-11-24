# Gallop Left Traced memory Events eq nil

Every left-biased gallop execution emits no merge-memory boundary events.
This is unconditional: it includes invalid-input failure, failed reads,
arithmetic-guard failure, and either exponential or binary fuel exhaustion.
