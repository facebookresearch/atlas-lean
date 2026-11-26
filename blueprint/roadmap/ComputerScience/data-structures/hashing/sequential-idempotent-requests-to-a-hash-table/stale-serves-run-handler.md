# Stale serves run handler

Lookup-level exclusion witness with no concurrency semantics: from one
snapshot with a lookup miss, every evaluation of the miss branch answers the
handler value and records the handler value, while chaining one serve makes
the next serve hit.
