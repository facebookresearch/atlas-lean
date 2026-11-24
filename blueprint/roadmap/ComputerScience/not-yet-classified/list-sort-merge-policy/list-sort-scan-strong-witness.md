# List Sort Scan Strong Witness

Strong scan witness: the replay split is supplemented by the historical
PowerSort forest carried by the real scan and an execution-indexed proof that
the displayed open state is the state actually passed to final collapse.

Unlike `PolicyTraceReplaySplit`, this structure has no transport theorem from
policy-event equality alone.
