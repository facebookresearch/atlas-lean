# Pending Push Event

Raw observations attached to the successful push of one formed run.

`naturalLength` is the length returned by run discovery, `target` is the
current adaptive-minrun target, and `remainingBefore` is the unscanned length
before this run is consumed.  Keeping all three separate makes both the
extended-short-run and already-long-natural-run cases observable.
